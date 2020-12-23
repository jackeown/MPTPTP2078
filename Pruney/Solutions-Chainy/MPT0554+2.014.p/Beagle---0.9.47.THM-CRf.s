%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 103 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

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
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_12,plain,(
    ! [A_6,B_29,D_44] :
      ( r2_hidden(k4_tarski('#skF_5'(A_6,B_29,k9_relat_1(A_6,B_29),D_44),D_44),A_6)
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_hidden('#skF_5'(A_78,B_79,k9_relat_1(A_78,B_79),D_80),B_79)
      | ~ r2_hidden(D_80,k9_relat_1(A_78,B_79))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_102,B_103,D_104,B_105] :
      ( r2_hidden('#skF_5'(A_102,B_103,k9_relat_1(A_102,B_103),D_104),B_105)
      | ~ r1_tarski(B_103,B_105)
      | ~ r2_hidden(D_104,k9_relat_1(A_102,B_103))
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_212,plain,(
    ! [D_138,B_137,B_136,B_139,A_140] :
      ( r2_hidden('#skF_5'(A_140,B_137,k9_relat_1(A_140,B_137),D_138),B_139)
      | ~ r1_tarski(B_136,B_139)
      | ~ r1_tarski(B_137,B_136)
      | ~ r2_hidden(D_138,k9_relat_1(A_140,B_137))
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_222,plain,(
    ! [A_141,B_142,D_143] :
      ( r2_hidden('#skF_5'(A_141,B_142,k9_relat_1(A_141,B_142),D_143),'#skF_7')
      | ~ r1_tarski(B_142,'#skF_6')
      | ~ r2_hidden(D_143,k9_relat_1(A_141,B_142))
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_8,plain,(
    ! [D_44,A_6,B_29,E_47] :
      ( r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ r2_hidden(E_47,B_29)
      | ~ r2_hidden(k4_tarski(E_47,D_44),A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    ! [B_166,A_167,D_165,A_168,D_164] :
      ( r2_hidden(D_165,k9_relat_1(A_168,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_5'(A_167,B_166,k9_relat_1(A_167,B_166),D_164),D_165),A_168)
      | ~ v1_relat_1(A_168)
      | ~ r1_tarski(B_166,'#skF_6')
      | ~ r2_hidden(D_164,k9_relat_1(A_167,B_166))
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_222,c_8])).

tff(c_276,plain,(
    ! [D_169,A_170,B_171] :
      ( r2_hidden(D_169,k9_relat_1(A_170,'#skF_7'))
      | ~ r1_tarski(B_171,'#skF_6')
      | ~ r2_hidden(D_169,k9_relat_1(A_170,B_171))
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_12,c_267])).

tff(c_349,plain,(
    ! [A_172,B_173,B_174] :
      ( r2_hidden('#skF_1'(k9_relat_1(A_172,B_173),B_174),k9_relat_1(A_172,'#skF_7'))
      | ~ r1_tarski(B_173,'#skF_6')
      | ~ v1_relat_1(A_172)
      | r1_tarski(k9_relat_1(A_172,B_173),B_174) ) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_364,plain,(
    ! [B_175,A_176] :
      ( ~ r1_tarski(B_175,'#skF_6')
      | ~ v1_relat_1(A_176)
      | r1_tarski(k9_relat_1(A_176,B_175),k9_relat_1(A_176,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_349,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k9_relat_1('#skF_8','#skF_6'),k9_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_377,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_364,c_26])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_37,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 2.63/1.39  
% 2.63/1.39  %Foreground sorts:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Background operators:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Foreground operators:
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.63/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.39  
% 2.63/1.40  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.63/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.63/1.40  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 2.63/1.40  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.40  tff(c_32, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.40  tff(c_37, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_32])).
% 2.63/1.40  tff(c_12, plain, (![A_6, B_29, D_44]: (r2_hidden(k4_tarski('#skF_5'(A_6, B_29, k9_relat_1(A_6, B_29), D_44), D_44), A_6) | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.40  tff(c_28, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.40  tff(c_114, plain, (![A_78, B_79, D_80]: (r2_hidden('#skF_5'(A_78, B_79, k9_relat_1(A_78, B_79), D_80), B_79) | ~r2_hidden(D_80, k9_relat_1(A_78, B_79)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.40  tff(c_160, plain, (![A_102, B_103, D_104, B_105]: (r2_hidden('#skF_5'(A_102, B_103, k9_relat_1(A_102, B_103), D_104), B_105) | ~r1_tarski(B_103, B_105) | ~r2_hidden(D_104, k9_relat_1(A_102, B_103)) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_114, c_2])).
% 2.63/1.40  tff(c_212, plain, (![D_138, B_137, B_136, B_139, A_140]: (r2_hidden('#skF_5'(A_140, B_137, k9_relat_1(A_140, B_137), D_138), B_139) | ~r1_tarski(B_136, B_139) | ~r1_tarski(B_137, B_136) | ~r2_hidden(D_138, k9_relat_1(A_140, B_137)) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.63/1.40  tff(c_222, plain, (![A_141, B_142, D_143]: (r2_hidden('#skF_5'(A_141, B_142, k9_relat_1(A_141, B_142), D_143), '#skF_7') | ~r1_tarski(B_142, '#skF_6') | ~r2_hidden(D_143, k9_relat_1(A_141, B_142)) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_28, c_212])).
% 2.63/1.40  tff(c_8, plain, (![D_44, A_6, B_29, E_47]: (r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~r2_hidden(E_47, B_29) | ~r2_hidden(k4_tarski(E_47, D_44), A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.40  tff(c_267, plain, (![B_166, A_167, D_165, A_168, D_164]: (r2_hidden(D_165, k9_relat_1(A_168, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_5'(A_167, B_166, k9_relat_1(A_167, B_166), D_164), D_165), A_168) | ~v1_relat_1(A_168) | ~r1_tarski(B_166, '#skF_6') | ~r2_hidden(D_164, k9_relat_1(A_167, B_166)) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_222, c_8])).
% 2.63/1.40  tff(c_276, plain, (![D_169, A_170, B_171]: (r2_hidden(D_169, k9_relat_1(A_170, '#skF_7')) | ~r1_tarski(B_171, '#skF_6') | ~r2_hidden(D_169, k9_relat_1(A_170, B_171)) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_12, c_267])).
% 2.63/1.40  tff(c_349, plain, (![A_172, B_173, B_174]: (r2_hidden('#skF_1'(k9_relat_1(A_172, B_173), B_174), k9_relat_1(A_172, '#skF_7')) | ~r1_tarski(B_173, '#skF_6') | ~v1_relat_1(A_172) | r1_tarski(k9_relat_1(A_172, B_173), B_174))), inference(resolution, [status(thm)], [c_6, c_276])).
% 2.63/1.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.40  tff(c_364, plain, (![B_175, A_176]: (~r1_tarski(B_175, '#skF_6') | ~v1_relat_1(A_176) | r1_tarski(k9_relat_1(A_176, B_175), k9_relat_1(A_176, '#skF_7')))), inference(resolution, [status(thm)], [c_349, c_4])).
% 2.63/1.40  tff(c_26, plain, (~r1_tarski(k9_relat_1('#skF_8', '#skF_6'), k9_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.40  tff(c_377, plain, (~r1_tarski('#skF_6', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_364, c_26])).
% 2.63/1.40  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_37, c_377])).
% 2.63/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  Inference rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Ref     : 0
% 2.63/1.40  #Sup     : 93
% 2.63/1.40  #Fact    : 0
% 2.63/1.40  #Define  : 0
% 2.63/1.40  #Split   : 1
% 2.63/1.40  #Chain   : 0
% 2.63/1.40  #Close   : 0
% 2.63/1.40  
% 2.63/1.40  Ordering : KBO
% 2.63/1.40  
% 2.63/1.40  Simplification rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Subsume      : 13
% 2.63/1.40  #Demod        : 2
% 2.63/1.40  #Tautology    : 1
% 2.63/1.40  #SimpNegUnit  : 0
% 2.63/1.40  #BackRed      : 0
% 2.63/1.40  
% 2.63/1.40  #Partial instantiations: 0
% 2.63/1.40  #Strategies tried      : 1
% 2.63/1.40  
% 2.63/1.40  Timing (in seconds)
% 2.63/1.40  ----------------------
% 2.63/1.40  Preprocessing        : 0.28
% 2.63/1.40  Parsing              : 0.15
% 2.63/1.40  CNF conversion       : 0.03
% 2.63/1.40  Main loop            : 0.32
% 2.63/1.40  Inferencing          : 0.13
% 2.63/1.40  Reduction            : 0.07
% 2.63/1.40  Demodulation         : 0.05
% 2.63/1.40  BG Simplification    : 0.02
% 2.63/1.40  Subsumption          : 0.09
% 2.63/1.40  Abstraction          : 0.01
% 2.63/1.40  MUC search           : 0.00
% 2.63/1.40  Cooper               : 0.00
% 2.63/1.40  Total                : 0.63
% 2.63/1.41  Index Insertion      : 0.00
% 2.63/1.41  Index Deletion       : 0.00
% 2.63/1.41  Index Matching       : 0.00
% 2.63/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
