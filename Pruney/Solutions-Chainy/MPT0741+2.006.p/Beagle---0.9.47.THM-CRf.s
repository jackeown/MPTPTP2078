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
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   50 (  96 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 229 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_49,axiom,(
    ! [A] :
      ( v2_ordinal1(A)
    <=> ! [B,C] :
          ~ ( r2_hidden(B,A)
            & r2_hidden(C,A)
            & ~ r2_hidden(B,C)
            & B != C
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( r2_hidden(B,A)
           => ( v3_ordinal1(B)
              & r1_tarski(B,A) ) )
       => v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

tff(f_55,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
    <=> ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

tff(f_70,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_166,plain,(
    ! [A_32] :
      ( '#skF_2'(A_32) != '#skF_3'(A_32)
      | v2_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | v1_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [B_17] :
      ( v3_ordinal1(B_17)
      | ~ r2_hidden(B_17,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,
    ( v3_ordinal1('#skF_1'('#skF_4'))
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_32])).

tff(c_75,plain,(
    v1_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_36,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21),A_21)
      | v2_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_41,plain,
    ( v3_ordinal1('#skF_2'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_32])).

tff(c_43,plain,(
    v2_ordinal1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_77,plain,(
    ! [A_27] :
      ( v3_ordinal1(A_27)
      | ~ v2_ordinal1(A_27)
      | ~ v1_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,
    ( ~ v2_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_28])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_43,c_86])).

tff(c_94,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_30,plain,(
    ! [B_17] :
      ( r1_tarski(B_17,'#skF_4')
      | ~ r2_hidden(B_17,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_4')
    | v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_30])).

tff(c_104,plain,(
    r1_tarski('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( ~ r1_tarski('#skF_1'(A_1),A_1)
      | v1_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_107])).

tff(c_113,plain,(
    ~ v2_ordinal1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_170,plain,(
    '#skF_2'('#skF_4') != '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_113])).

tff(c_135,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | v2_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,
    ( v3_ordinal1('#skF_3'('#skF_4'))
    | v2_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_32])).

tff(c_142,plain,(
    v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_139])).

tff(c_112,plain,(
    v3_ordinal1('#skF_2'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_217,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | B_40 = A_41
      | r2_hidden(A_41,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2'(A_5),'#skF_3'(A_5))
      | v2_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_325,plain,(
    ! [A_49] :
      ( v2_ordinal1(A_49)
      | '#skF_2'(A_49) = '#skF_3'(A_49)
      | r2_hidden('#skF_3'(A_49),'#skF_2'(A_49))
      | ~ v3_ordinal1('#skF_2'(A_49))
      | ~ v3_ordinal1('#skF_3'(A_49)) ) ),
    inference(resolution,[status(thm)],[c_217,c_14])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_3'(A_5),'#skF_2'(A_5))
      | v2_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_337,plain,(
    ! [A_50] :
      ( v2_ordinal1(A_50)
      | '#skF_2'(A_50) = '#skF_3'(A_50)
      | ~ v3_ordinal1('#skF_2'(A_50))
      | ~ v3_ordinal1('#skF_3'(A_50)) ) ),
    inference(resolution,[status(thm)],[c_325,c_10])).

tff(c_343,plain,
    ( v2_ordinal1('#skF_4')
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4')
    | ~ v3_ordinal1('#skF_3'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_112,c_337])).

tff(c_347,plain,
    ( v2_ordinal1('#skF_4')
    | '#skF_2'('#skF_4') = '#skF_3'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_343])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_113,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.24  %$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.03/1.24  
% 2.03/1.24  %Foreground sorts:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Background operators:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Foreground operators:
% 2.03/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.24  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.03/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.03/1.24  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.24  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.24  
% 2.03/1.25  tff(f_49, axiom, (![A]: (v2_ordinal1(A) <=> (![B, C]: ~((((r2_hidden(B, A) & r2_hidden(C, A)) & ~r2_hidden(B, C)) & ~(B = C)) & ~r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_ordinal1)).
% 2.03/1.25  tff(f_32, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.03/1.25  tff(f_80, negated_conjecture, ~(![A]: ((![B]: (r2_hidden(B, A) => (v3_ordinal1(B) & r1_tarski(B, A)))) => v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_ordinal1)).
% 2.03/1.25  tff(f_55, axiom, (![A]: (v3_ordinal1(A) <=> (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_ordinal1)).
% 2.03/1.25  tff(f_70, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.03/1.25  tff(c_166, plain, (![A_32]: ('#skF_2'(A_32)!='#skF_3'(A_32) | v2_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.25  tff(c_64, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | v1_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.25  tff(c_32, plain, (![B_17]: (v3_ordinal1(B_17) | ~r2_hidden(B_17, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_74, plain, (v3_ordinal1('#skF_1'('#skF_4')) | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_32])).
% 2.03/1.25  tff(c_75, plain, (v1_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 2.03/1.25  tff(c_36, plain, (![A_21]: (r2_hidden('#skF_2'(A_21), A_21) | v2_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.25  tff(c_41, plain, (v3_ordinal1('#skF_2'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_32])).
% 2.03/1.25  tff(c_43, plain, (v2_ordinal1('#skF_4')), inference(splitLeft, [status(thm)], [c_41])).
% 2.03/1.25  tff(c_77, plain, (![A_27]: (v3_ordinal1(A_27) | ~v2_ordinal1(A_27) | ~v1_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.25  tff(c_28, plain, (~v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_86, plain, (~v2_ordinal1('#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_28])).
% 2.03/1.25  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_43, c_86])).
% 2.03/1.25  tff(c_94, plain, (~v1_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 2.03/1.25  tff(c_30, plain, (![B_17]: (r1_tarski(B_17, '#skF_4') | ~r2_hidden(B_17, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_73, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4') | v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_30])).
% 2.03/1.25  tff(c_104, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_73])).
% 2.03/1.25  tff(c_4, plain, (![A_1]: (~r1_tarski('#skF_1'(A_1), A_1) | v1_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.25  tff(c_107, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_4])).
% 2.03/1.25  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_107])).
% 2.03/1.25  tff(c_113, plain, (~v2_ordinal1('#skF_4')), inference(splitRight, [status(thm)], [c_41])).
% 2.03/1.25  tff(c_170, plain, ('#skF_2'('#skF_4')!='#skF_3'('#skF_4')), inference(resolution, [status(thm)], [c_166, c_113])).
% 2.03/1.25  tff(c_135, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | v2_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.25  tff(c_139, plain, (v3_ordinal1('#skF_3'('#skF_4')) | v2_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_32])).
% 2.03/1.25  tff(c_142, plain, (v3_ordinal1('#skF_3'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_113, c_139])).
% 2.03/1.25  tff(c_112, plain, (v3_ordinal1('#skF_2'('#skF_4'))), inference(splitRight, [status(thm)], [c_41])).
% 2.03/1.25  tff(c_217, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | B_40=A_41 | r2_hidden(A_41, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.03/1.25  tff(c_14, plain, (![A_5]: (~r2_hidden('#skF_2'(A_5), '#skF_3'(A_5)) | v2_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.25  tff(c_325, plain, (![A_49]: (v2_ordinal1(A_49) | '#skF_2'(A_49)='#skF_3'(A_49) | r2_hidden('#skF_3'(A_49), '#skF_2'(A_49)) | ~v3_ordinal1('#skF_2'(A_49)) | ~v3_ordinal1('#skF_3'(A_49)))), inference(resolution, [status(thm)], [c_217, c_14])).
% 2.03/1.25  tff(c_10, plain, (![A_5]: (~r2_hidden('#skF_3'(A_5), '#skF_2'(A_5)) | v2_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.25  tff(c_337, plain, (![A_50]: (v2_ordinal1(A_50) | '#skF_2'(A_50)='#skF_3'(A_50) | ~v3_ordinal1('#skF_2'(A_50)) | ~v3_ordinal1('#skF_3'(A_50)))), inference(resolution, [status(thm)], [c_325, c_10])).
% 2.03/1.25  tff(c_343, plain, (v2_ordinal1('#skF_4') | '#skF_2'('#skF_4')='#skF_3'('#skF_4') | ~v3_ordinal1('#skF_3'('#skF_4'))), inference(resolution, [status(thm)], [c_112, c_337])).
% 2.03/1.25  tff(c_347, plain, (v2_ordinal1('#skF_4') | '#skF_2'('#skF_4')='#skF_3'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_343])).
% 2.03/1.25  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_113, c_347])).
% 2.03/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  Inference rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Ref     : 0
% 2.03/1.25  #Sup     : 54
% 2.03/1.25  #Fact    : 4
% 2.03/1.25  #Define  : 0
% 2.03/1.25  #Split   : 3
% 2.03/1.25  #Chain   : 0
% 2.03/1.25  #Close   : 0
% 2.03/1.25  
% 2.03/1.25  Ordering : KBO
% 2.03/1.25  
% 2.03/1.25  Simplification rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Subsume      : 11
% 2.03/1.25  #Demod        : 7
% 2.03/1.25  #Tautology    : 15
% 2.03/1.25  #SimpNegUnit  : 6
% 2.03/1.25  #BackRed      : 0
% 2.03/1.25  
% 2.03/1.25  #Partial instantiations: 0
% 2.03/1.25  #Strategies tried      : 1
% 2.03/1.25  
% 2.03/1.25  Timing (in seconds)
% 2.03/1.25  ----------------------
% 2.03/1.25  Preprocessing        : 0.28
% 2.03/1.25  Parsing              : 0.14
% 2.03/1.25  CNF conversion       : 0.02
% 2.03/1.25  Main loop            : 0.22
% 2.03/1.25  Inferencing          : 0.10
% 2.03/1.25  Reduction            : 0.05
% 2.03/1.25  Demodulation         : 0.03
% 2.03/1.25  BG Simplification    : 0.02
% 2.03/1.25  Subsumption          : 0.04
% 2.03/1.25  Abstraction          : 0.01
% 2.03/1.25  MUC search           : 0.00
% 2.03/1.25  Cooper               : 0.00
% 2.03/1.25  Total                : 0.53
% 2.03/1.25  Index Insertion      : 0.00
% 2.03/1.25  Index Deletion       : 0.00
% 2.03/1.25  Index Matching       : 0.00
% 2.03/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
