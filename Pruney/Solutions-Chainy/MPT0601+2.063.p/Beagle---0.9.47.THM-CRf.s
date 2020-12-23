%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 103 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,B_70)
      | ~ r2_hidden(C_71,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_224])).

tff(c_32,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k4_tarski(A_46,B_47),C_48)
      | ~ r2_hidden(B_47,k11_relat_1(C_48,A_46))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k1_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(C_24,D_27),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_109,plain,(
    ! [A_52,C_53,B_54] :
      ( r2_hidden(A_52,k1_relat_1(C_53))
      | ~ r2_hidden(B_54,k11_relat_1(C_53,A_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_93,c_16])).

tff(c_185,plain,(
    ! [A_60,C_61] :
      ( r2_hidden(A_60,k1_relat_1(C_61))
      | ~ v1_relat_1(C_61)
      | k11_relat_1(C_61,A_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_200,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_185,c_46])).

tff(c_209,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_200])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_209])).

tff(c_212,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_219,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_38])).

tff(c_378,plain,(
    ! [C_94,A_95] :
      ( r2_hidden(k4_tarski(C_94,'#skF_6'(A_95,k1_relat_1(A_95),C_94)),A_95)
      | ~ r2_hidden(C_94,k1_relat_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [B_29,C_30,A_28] :
      ( r2_hidden(B_29,k11_relat_1(C_30,A_28))
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1343,plain,(
    ! [A_149,C_150] :
      ( r2_hidden('#skF_6'(A_149,k1_relat_1(A_149),C_150),k11_relat_1(A_149,C_150))
      | ~ v1_relat_1(A_149)
      | ~ r2_hidden(C_150,k1_relat_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_378,c_28])).

tff(c_1363,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_1343])).

tff(c_1368,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_30,c_1363])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_1368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.57  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 3.38/1.57  
% 3.38/1.57  %Foreground sorts:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Background operators:
% 3.38/1.57  
% 3.38/1.57  
% 3.38/1.57  %Foreground operators:
% 3.38/1.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.38/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.38/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.38/1.57  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.38/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.38/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.38/1.57  
% 3.62/1.58  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.62/1.58  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.62/1.58  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.62/1.58  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.62/1.58  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.62/1.58  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.62/1.58  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.58  tff(c_224, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, B_70) | ~r2_hidden(C_71, A_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.58  tff(c_227, plain, (![C_71]: (~r2_hidden(C_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_224])).
% 3.62/1.58  tff(c_32, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.58  tff(c_46, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.62/1.58  tff(c_38, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.58  tff(c_48, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_38])).
% 3.62/1.58  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.58  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.62/1.58  tff(c_93, plain, (![A_46, B_47, C_48]: (r2_hidden(k4_tarski(A_46, B_47), C_48) | ~r2_hidden(B_47, k11_relat_1(C_48, A_46)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.62/1.58  tff(c_16, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k1_relat_1(A_9)) | ~r2_hidden(k4_tarski(C_24, D_27), A_9))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.62/1.58  tff(c_109, plain, (![A_52, C_53, B_54]: (r2_hidden(A_52, k1_relat_1(C_53)) | ~r2_hidden(B_54, k11_relat_1(C_53, A_52)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_93, c_16])).
% 3.62/1.58  tff(c_185, plain, (![A_60, C_61]: (r2_hidden(A_60, k1_relat_1(C_61)) | ~v1_relat_1(C_61) | k11_relat_1(C_61, A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_109])).
% 3.62/1.58  tff(c_200, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_185, c_46])).
% 3.62/1.58  tff(c_209, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_200])).
% 3.62/1.58  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_209])).
% 3.62/1.58  tff(c_212, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.62/1.58  tff(c_219, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_38])).
% 3.62/1.58  tff(c_378, plain, (![C_94, A_95]: (r2_hidden(k4_tarski(C_94, '#skF_6'(A_95, k1_relat_1(A_95), C_94)), A_95) | ~r2_hidden(C_94, k1_relat_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.62/1.58  tff(c_28, plain, (![B_29, C_30, A_28]: (r2_hidden(B_29, k11_relat_1(C_30, A_28)) | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.62/1.58  tff(c_1343, plain, (![A_149, C_150]: (r2_hidden('#skF_6'(A_149, k1_relat_1(A_149), C_150), k11_relat_1(A_149, C_150)) | ~v1_relat_1(A_149) | ~r2_hidden(C_150, k1_relat_1(A_149)))), inference(resolution, [status(thm)], [c_378, c_28])).
% 3.62/1.58  tff(c_1363, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_1343])).
% 3.62/1.58  tff(c_1368, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_30, c_1363])).
% 3.62/1.58  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_1368])).
% 3.62/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.58  
% 3.62/1.58  Inference rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Ref     : 0
% 3.62/1.58  #Sup     : 284
% 3.62/1.58  #Fact    : 0
% 3.62/1.58  #Define  : 0
% 3.62/1.58  #Split   : 3
% 3.62/1.58  #Chain   : 0
% 3.62/1.58  #Close   : 0
% 3.62/1.58  
% 3.62/1.58  Ordering : KBO
% 3.62/1.58  
% 3.62/1.58  Simplification rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Subsume      : 62
% 3.62/1.58  #Demod        : 136
% 3.62/1.58  #Tautology    : 65
% 3.62/1.58  #SimpNegUnit  : 51
% 3.62/1.58  #BackRed      : 2
% 3.62/1.58  
% 3.62/1.58  #Partial instantiations: 0
% 3.62/1.58  #Strategies tried      : 1
% 3.62/1.58  
% 3.62/1.58  Timing (in seconds)
% 3.62/1.58  ----------------------
% 3.62/1.58  Preprocessing        : 0.30
% 3.62/1.58  Parsing              : 0.16
% 3.62/1.58  CNF conversion       : 0.02
% 3.62/1.58  Main loop            : 0.47
% 3.62/1.58  Inferencing          : 0.18
% 3.62/1.58  Reduction            : 0.12
% 3.62/1.58  Demodulation         : 0.07
% 3.62/1.58  BG Simplification    : 0.02
% 3.62/1.58  Subsumption          : 0.11
% 3.62/1.58  Abstraction          : 0.03
% 3.62/1.58  MUC search           : 0.00
% 3.62/1.58  Cooper               : 0.00
% 3.62/1.58  Total                : 0.79
% 3.62/1.58  Index Insertion      : 0.00
% 3.62/1.58  Index Deletion       : 0.00
% 3.62/1.58  Index Matching       : 0.00
% 3.62/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
