%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 207 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,B)
            & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k8_relat_1(A_38,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,
    ( r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11')))
    | r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11')))
    | r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_20,plain,(
    ! [A_19,C_34] :
      ( r2_hidden(k4_tarski('#skF_8'(A_19,k2_relat_1(A_19),C_34),C_34),A_19)
      | ~ r2_hidden(C_34,k2_relat_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [D_74,E_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(D_74,E_75),k8_relat_1(A_76,B_77))
      | ~ r2_hidden(k4_tarski(D_74,E_75),B_77)
      | ~ r2_hidden(E_75,A_76)
      | ~ v1_relat_1(k8_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k2_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(D_37,C_34),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_170,plain,(
    ! [E_78,A_79,B_80,D_81] :
      ( r2_hidden(E_78,k2_relat_1(k8_relat_1(A_79,B_80)))
      | ~ r2_hidden(k4_tarski(D_81,E_78),B_80)
      | ~ r2_hidden(E_78,A_79)
      | ~ v1_relat_1(k8_relat_1(A_79,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_153,c_22])).

tff(c_183,plain,(
    ! [C_82,A_83,A_84] :
      ( r2_hidden(C_82,k2_relat_1(k8_relat_1(A_83,A_84)))
      | ~ r2_hidden(C_82,A_83)
      | ~ v1_relat_1(k8_relat_1(A_83,A_84))
      | ~ v1_relat_1(A_84)
      | ~ r2_hidden(C_82,k2_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_36])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_183,c_53])).

tff(c_214,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_48,c_202])).

tff(c_218,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_214])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_224,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_223,plain,(
    r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_284,plain,(
    ! [D_103,E_104,B_105,A_106] :
      ( r2_hidden(k4_tarski(D_103,E_104),B_105)
      | ~ r2_hidden(k4_tarski(D_103,E_104),k8_relat_1(A_106,B_105))
      | ~ v1_relat_1(k8_relat_1(A_106,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_444,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden(k4_tarski('#skF_8'(k8_relat_1(A_135,B_136),k2_relat_1(k8_relat_1(A_135,B_136)),C_137),C_137),B_136)
      | ~ v1_relat_1(k8_relat_1(A_135,B_136))
      | ~ v1_relat_1(B_136)
      | ~ r2_hidden(C_137,k2_relat_1(k8_relat_1(A_135,B_136))) ) ),
    inference(resolution,[status(thm)],[c_20,c_284])).

tff(c_474,plain,(
    ! [C_138,B_139,A_140] :
      ( r2_hidden(C_138,k2_relat_1(B_139))
      | ~ v1_relat_1(k8_relat_1(A_140,B_139))
      | ~ v1_relat_1(B_139)
      | ~ r2_hidden(C_138,k2_relat_1(k8_relat_1(A_140,B_139))) ) ),
    inference(resolution,[status(thm)],[c_444,c_22])).

tff(c_520,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_223,c_474])).

tff(c_534,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_520])).

tff(c_535,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_534])).

tff(c_599,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_535])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_599])).

tff(c_605,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_604,plain,(
    r2_hidden('#skF_9',k2_relat_1(k8_relat_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_617,plain,(
    ! [E_154,A_155,D_156,B_157] :
      ( r2_hidden(E_154,A_155)
      | ~ r2_hidden(k4_tarski(D_156,E_154),k8_relat_1(A_155,B_157))
      | ~ v1_relat_1(k8_relat_1(A_155,B_157))
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_623,plain,(
    ! [C_158,A_159,B_160] :
      ( r2_hidden(C_158,A_159)
      | ~ v1_relat_1(k8_relat_1(A_159,B_160))
      | ~ v1_relat_1(B_160)
      | ~ r2_hidden(C_158,k2_relat_1(k8_relat_1(A_159,B_160))) ) ),
    inference(resolution,[status(thm)],[c_20,c_617])).

tff(c_634,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_604,c_623])).

tff(c_639,plain,
    ( r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_634])).

tff(c_640,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_639])).

tff(c_643,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_640])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.99  
% 3.70/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.99  %$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 3.70/1.99  
% 3.70/1.99  %Foreground sorts:
% 3.70/1.99  
% 3.70/1.99  
% 3.70/1.99  %Background operators:
% 3.70/1.99  
% 3.70/1.99  
% 3.70/1.99  %Foreground operators:
% 3.70/1.99  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.70/1.99  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.70/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.99  tff('#skF_11', type, '#skF_11': $i).
% 3.70/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.70/1.99  tff('#skF_10', type, '#skF_10': $i).
% 3.70/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.99  tff('#skF_9', type, '#skF_9': $i).
% 3.70/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.70/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.99  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.70/1.99  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.70/1.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.70/1.99  
% 3.70/2.01  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_relat_1)).
% 3.70/2.01  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.70/2.01  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.70/2.01  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 3.70/2.01  tff(c_34, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/2.01  tff(c_32, plain, (![A_38, B_39]: (v1_relat_1(k8_relat_1(A_38, B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.70/2.01  tff(c_42, plain, (r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11'))) | r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/2.01  tff(c_50, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.70/2.01  tff(c_46, plain, (r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11'))) | r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/2.01  tff(c_48, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_46])).
% 3.70/2.01  tff(c_20, plain, (![A_19, C_34]: (r2_hidden(k4_tarski('#skF_8'(A_19, k2_relat_1(A_19), C_34), C_34), A_19) | ~r2_hidden(C_34, k2_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/2.01  tff(c_153, plain, (![D_74, E_75, A_76, B_77]: (r2_hidden(k4_tarski(D_74, E_75), k8_relat_1(A_76, B_77)) | ~r2_hidden(k4_tarski(D_74, E_75), B_77) | ~r2_hidden(E_75, A_76) | ~v1_relat_1(k8_relat_1(A_76, B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/2.01  tff(c_22, plain, (![C_34, A_19, D_37]: (r2_hidden(C_34, k2_relat_1(A_19)) | ~r2_hidden(k4_tarski(D_37, C_34), A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/2.01  tff(c_170, plain, (![E_78, A_79, B_80, D_81]: (r2_hidden(E_78, k2_relat_1(k8_relat_1(A_79, B_80))) | ~r2_hidden(k4_tarski(D_81, E_78), B_80) | ~r2_hidden(E_78, A_79) | ~v1_relat_1(k8_relat_1(A_79, B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_153, c_22])).
% 3.70/2.01  tff(c_183, plain, (![C_82, A_83, A_84]: (r2_hidden(C_82, k2_relat_1(k8_relat_1(A_83, A_84))) | ~r2_hidden(C_82, A_83) | ~v1_relat_1(k8_relat_1(A_83, A_84)) | ~v1_relat_1(A_84) | ~r2_hidden(C_82, k2_relat_1(A_84)))), inference(resolution, [status(thm)], [c_20, c_170])).
% 3.70/2.01  tff(c_36, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_11')) | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/2.01  tff(c_53, plain, (~r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_36])).
% 3.70/2.01  tff(c_202, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k8_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_183, c_53])).
% 3.70/2.01  tff(c_214, plain, (~v1_relat_1(k8_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34, c_48, c_202])).
% 3.70/2.01  tff(c_218, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_214])).
% 3.70/2.01  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_218])).
% 3.70/2.01  tff(c_224, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_42])).
% 3.70/2.01  tff(c_223, plain, (r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_42])).
% 3.70/2.01  tff(c_284, plain, (![D_103, E_104, B_105, A_106]: (r2_hidden(k4_tarski(D_103, E_104), B_105) | ~r2_hidden(k4_tarski(D_103, E_104), k8_relat_1(A_106, B_105)) | ~v1_relat_1(k8_relat_1(A_106, B_105)) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/2.01  tff(c_444, plain, (![A_135, B_136, C_137]: (r2_hidden(k4_tarski('#skF_8'(k8_relat_1(A_135, B_136), k2_relat_1(k8_relat_1(A_135, B_136)), C_137), C_137), B_136) | ~v1_relat_1(k8_relat_1(A_135, B_136)) | ~v1_relat_1(B_136) | ~r2_hidden(C_137, k2_relat_1(k8_relat_1(A_135, B_136))))), inference(resolution, [status(thm)], [c_20, c_284])).
% 3.70/2.01  tff(c_474, plain, (![C_138, B_139, A_140]: (r2_hidden(C_138, k2_relat_1(B_139)) | ~v1_relat_1(k8_relat_1(A_140, B_139)) | ~v1_relat_1(B_139) | ~r2_hidden(C_138, k2_relat_1(k8_relat_1(A_140, B_139))))), inference(resolution, [status(thm)], [c_444, c_22])).
% 3.70/2.01  tff(c_520, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11')) | ~v1_relat_1(k8_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_223, c_474])).
% 3.70/2.01  tff(c_534, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11')) | ~v1_relat_1(k8_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_520])).
% 3.70/2.01  tff(c_535, plain, (~v1_relat_1(k8_relat_1('#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_224, c_534])).
% 3.70/2.01  tff(c_599, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_535])).
% 3.70/2.01  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_599])).
% 3.70/2.01  tff(c_605, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_46])).
% 3.70/2.01  tff(c_604, plain, (r2_hidden('#skF_9', k2_relat_1(k8_relat_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_46])).
% 3.70/2.01  tff(c_617, plain, (![E_154, A_155, D_156, B_157]: (r2_hidden(E_154, A_155) | ~r2_hidden(k4_tarski(D_156, E_154), k8_relat_1(A_155, B_157)) | ~v1_relat_1(k8_relat_1(A_155, B_157)) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.70/2.01  tff(c_623, plain, (![C_158, A_159, B_160]: (r2_hidden(C_158, A_159) | ~v1_relat_1(k8_relat_1(A_159, B_160)) | ~v1_relat_1(B_160) | ~r2_hidden(C_158, k2_relat_1(k8_relat_1(A_159, B_160))))), inference(resolution, [status(thm)], [c_20, c_617])).
% 3.70/2.01  tff(c_634, plain, (r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k8_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_604, c_623])).
% 3.70/2.01  tff(c_639, plain, (r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k8_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_634])).
% 3.70/2.01  tff(c_640, plain, (~v1_relat_1(k8_relat_1('#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_605, c_639])).
% 3.70/2.01  tff(c_643, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_640])).
% 3.70/2.01  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_643])).
% 3.70/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/2.01  
% 3.70/2.01  Inference rules
% 3.70/2.01  ----------------------
% 3.70/2.01  #Ref     : 0
% 3.70/2.01  #Sup     : 120
% 3.70/2.01  #Fact    : 0
% 3.70/2.01  #Define  : 0
% 3.70/2.01  #Split   : 2
% 3.70/2.01  #Chain   : 0
% 3.70/2.01  #Close   : 0
% 3.70/2.01  
% 3.70/2.01  Ordering : KBO
% 3.70/2.01  
% 3.70/2.01  Simplification rules
% 3.70/2.01  ----------------------
% 3.70/2.01  #Subsume      : 2
% 3.70/2.01  #Demod        : 16
% 3.70/2.01  #Tautology    : 19
% 3.70/2.01  #SimpNegUnit  : 2
% 3.70/2.01  #BackRed      : 0
% 3.70/2.01  
% 3.70/2.01  #Partial instantiations: 0
% 3.70/2.01  #Strategies tried      : 1
% 3.70/2.01  
% 3.70/2.01  Timing (in seconds)
% 3.70/2.01  ----------------------
% 3.70/2.02  Preprocessing        : 0.45
% 3.70/2.02  Parsing              : 0.22
% 3.70/2.02  CNF conversion       : 0.04
% 3.70/2.02  Main loop            : 0.61
% 3.70/2.02  Inferencing          : 0.23
% 3.70/2.02  Reduction            : 0.14
% 3.70/2.02  Demodulation         : 0.10
% 3.70/2.02  BG Simplification    : 0.04
% 3.70/2.02  Subsumption          : 0.15
% 3.70/2.02  Abstraction          : 0.03
% 3.70/2.02  MUC search           : 0.00
% 3.70/2.02  Cooper               : 0.00
% 3.70/2.02  Total                : 1.11
% 3.70/2.02  Index Insertion      : 0.00
% 3.70/2.02  Index Deletion       : 0.00
% 3.70/2.02  Index Matching       : 0.00
% 3.70/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
