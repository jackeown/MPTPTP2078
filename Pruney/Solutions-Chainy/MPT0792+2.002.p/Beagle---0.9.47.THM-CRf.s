%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  82 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 234 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C))
            & ! [D] :
                ( r2_hidden(D,k1_wellord1(C,A))
               => ( r2_hidden(k4_tarski(D,B),C)
                  & D != B ) ) )
         => r2_hidden(k4_tarski(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_wellord1)).

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
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(c_30,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    v2_wellord1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    r2_hidden('#skF_4',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [D_22] :
      ( r2_hidden(k4_tarski(D_22,'#skF_5'),'#skF_6')
      | ~ r2_hidden(D_22,k1_wellord1('#skF_6','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_129,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k1_wellord1(A_48,B_49))
      | ~ r2_hidden(k4_tarski(D_47,B_49),A_48)
      | D_47 = B_49
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,k1_wellord1('#skF_6','#skF_5'))
      | D_22 = '#skF_5'
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_22,k1_wellord1('#skF_6','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_144,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,k1_wellord1('#skF_6','#skF_5'))
      | D_50 = '#skF_5'
      | ~ r2_hidden(D_50,k1_wellord1('#skF_6','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_138])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_268,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k1_wellord1('#skF_6','#skF_5'))
      | '#skF_1'(A_84,k1_wellord1('#skF_6','#skF_5')) = '#skF_5'
      | ~ r2_hidden('#skF_1'(A_84,k1_wellord1('#skF_6','#skF_5')),k1_wellord1('#skF_6','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_278,plain,
    ( '#skF_1'(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) = '#skF_5'
    | r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_279,plain,(
    r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_347,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(k4_tarski(A_91,B_92),C_93)
      | ~ r1_tarski(k1_wellord1(C_93,A_91),k1_wellord1(C_93,B_92))
      | ~ r2_hidden(B_92,k3_relat_1(C_93))
      | ~ r2_hidden(A_91,k3_relat_1(C_93))
      | ~ v2_wellord1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_354,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_279,c_347])).

tff(c_367,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_354])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_367])).

tff(c_371,plain,(
    ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_5',k1_wellord1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_370,plain,(
    '#skF_1'(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_384,plain,
    ( r2_hidden('#skF_5',k1_wellord1('#skF_6','#skF_4'))
    | r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_6])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_40,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.36  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.66/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.36  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.66/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.36  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.66/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.36  
% 2.66/1.37  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & (![D]: (r2_hidden(D, k1_wellord1(C, A)) => (r2_hidden(k4_tarski(D, B), C) & ~(D = B))))) => r2_hidden(k4_tarski(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_wellord1)).
% 2.66/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.37  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.66/1.37  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 2.66/1.37  tff(c_30, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_38, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_36, plain, (v2_wellord1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_34, plain, (r2_hidden('#skF_4', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_32, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_42, plain, (![D_22]: (r2_hidden(k4_tarski(D_22, '#skF_5'), '#skF_6') | ~r2_hidden(D_22, k1_wellord1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_129, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, k1_wellord1(A_48, B_49)) | ~r2_hidden(k4_tarski(D_47, B_49), A_48) | D_47=B_49 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.37  tff(c_138, plain, (![D_22]: (r2_hidden(D_22, k1_wellord1('#skF_6', '#skF_5')) | D_22='#skF_5' | ~v1_relat_1('#skF_6') | ~r2_hidden(D_22, k1_wellord1('#skF_6', '#skF_4')))), inference(resolution, [status(thm)], [c_42, c_129])).
% 2.66/1.37  tff(c_144, plain, (![D_50]: (r2_hidden(D_50, k1_wellord1('#skF_6', '#skF_5')) | D_50='#skF_5' | ~r2_hidden(D_50, k1_wellord1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_138])).
% 2.66/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.37  tff(c_268, plain, (![A_84]: (r1_tarski(A_84, k1_wellord1('#skF_6', '#skF_5')) | '#skF_1'(A_84, k1_wellord1('#skF_6', '#skF_5'))='#skF_5' | ~r2_hidden('#skF_1'(A_84, k1_wellord1('#skF_6', '#skF_5')), k1_wellord1('#skF_6', '#skF_4')))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.66/1.37  tff(c_278, plain, ('#skF_1'(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))='#skF_5' | r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.66/1.37  tff(c_279, plain, (r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_278])).
% 2.66/1.37  tff(c_347, plain, (![A_91, B_92, C_93]: (r2_hidden(k4_tarski(A_91, B_92), C_93) | ~r1_tarski(k1_wellord1(C_93, A_91), k1_wellord1(C_93, B_92)) | ~r2_hidden(B_92, k3_relat_1(C_93)) | ~r2_hidden(A_91, k3_relat_1(C_93)) | ~v2_wellord1(C_93) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.37  tff(c_354, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k3_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_279, c_347])).
% 2.66/1.37  tff(c_367, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_354])).
% 2.66/1.37  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_367])).
% 2.66/1.37  tff(c_371, plain, (~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_278])).
% 2.66/1.37  tff(c_40, plain, (~r2_hidden('#skF_5', k1_wellord1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.66/1.37  tff(c_370, plain, ('#skF_1'(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_278])).
% 2.66/1.37  tff(c_384, plain, (r2_hidden('#skF_5', k1_wellord1('#skF_6', '#skF_4')) | r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_6])).
% 2.66/1.37  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_40, c_384])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 76
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 3
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 11
% 2.66/1.37  #Demod        : 17
% 2.66/1.37  #Tautology    : 5
% 2.66/1.37  #SimpNegUnit  : 6
% 2.66/1.37  #BackRed      : 0
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.37  Preprocessing        : 0.30
% 2.66/1.37  Parsing              : 0.16
% 2.66/1.37  CNF conversion       : 0.02
% 2.66/1.37  Main loop            : 0.30
% 2.66/1.37  Inferencing          : 0.11
% 2.66/1.37  Reduction            : 0.07
% 2.66/1.37  Demodulation         : 0.05
% 2.66/1.37  BG Simplification    : 0.02
% 2.66/1.37  Subsumption          : 0.08
% 2.66/1.37  Abstraction          : 0.01
% 2.66/1.37  MUC search           : 0.00
% 2.66/1.37  Cooper               : 0.00
% 2.66/1.37  Total                : 0.63
% 2.66/1.37  Index Insertion      : 0.00
% 2.66/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
