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
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 209 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(k7_relat_1(A_42,B_43))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_10',k7_relat_1('#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_1'(A_51,B_52),B_52)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_30,plain,(
    ! [A_25,B_35] :
      ( r2_hidden(k4_tarski('#skF_6'(A_25,B_35),'#skF_7'(A_25,B_35)),A_25)
      | r1_tarski(A_25,B_35)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    r1_tarski(k1_relat_1('#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,(
    ! [B_57,A_58] :
      ( k7_relat_1(B_57,A_58) = B_57
      | ~ r1_tarski(k1_relat_1(B_57),A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,
    ( k7_relat_1('#skF_10','#skF_8') = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_40,c_58])).

tff(c_69,plain,(
    k7_relat_1('#skF_10','#skF_8') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_65])).

tff(c_181,plain,(
    ! [D_87,B_88,E_89,A_90] :
      ( r2_hidden(D_87,B_88)
      | ~ r2_hidden(k4_tarski(D_87,E_89),k7_relat_1(A_90,B_88))
      | ~ v1_relat_1(k7_relat_1(A_90,B_88))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [D_87,E_89] :
      ( r2_hidden(D_87,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_87,E_89),'#skF_10')
      | ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_181])).

tff(c_195,plain,(
    ! [D_91,E_92] :
      ( r2_hidden(D_91,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_91,E_92),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_69,c_191])).

tff(c_199,plain,(
    ! [B_35] :
      ( r2_hidden('#skF_6'('#skF_10',B_35),'#skF_8')
      | r1_tarski('#skF_10',B_35)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_202,plain,(
    ! [B_35] :
      ( r2_hidden('#skF_6'('#skF_10',B_35),'#skF_8')
      | r1_tarski('#skF_10',B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_199])).

tff(c_38,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_100,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(k4_tarski('#skF_6'(A_63,B_64),'#skF_7'(A_63,B_64)),A_63)
      | r1_tarski(A_63,B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_247,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden(k4_tarski('#skF_6'(A_107,B_108),'#skF_7'(A_107,B_108)),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r1_tarski(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_386,plain,(
    ! [A_152,B_153,B_154,B_155] :
      ( r2_hidden(k4_tarski('#skF_6'(A_152,B_153),'#skF_7'(A_152,B_153)),B_154)
      | ~ r1_tarski(B_155,B_154)
      | ~ r1_tarski(A_152,B_155)
      | r1_tarski(A_152,B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_247,c_2])).

tff(c_395,plain,(
    ! [A_152,B_153] :
      ( r2_hidden(k4_tarski('#skF_6'(A_152,B_153),'#skF_7'(A_152,B_153)),'#skF_9')
      | ~ r1_tarski(A_152,'#skF_10')
      | r1_tarski(A_152,B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_329,plain,(
    ! [D_134,E_135,A_136,B_137] :
      ( r2_hidden(k4_tarski(D_134,E_135),k7_relat_1(A_136,B_137))
      | ~ r2_hidden(k4_tarski(D_134,E_135),A_136)
      | ~ r2_hidden(D_134,B_137)
      | ~ v1_relat_1(k7_relat_1(A_136,B_137))
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_25,B_35] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_25,B_35),'#skF_7'(A_25,B_35)),B_35)
      | r1_tarski(A_25,B_35)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2354,plain,(
    ! [A_381,A_382,B_383] :
      ( r1_tarski(A_381,k7_relat_1(A_382,B_383))
      | ~ v1_relat_1(A_381)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_381,k7_relat_1(A_382,B_383)),'#skF_7'(A_381,k7_relat_1(A_382,B_383))),A_382)
      | ~ r2_hidden('#skF_6'(A_381,k7_relat_1(A_382,B_383)),B_383)
      | ~ v1_relat_1(k7_relat_1(A_382,B_383))
      | ~ v1_relat_1(A_382) ) ),
    inference(resolution,[status(thm)],[c_329,c_28])).

tff(c_2382,plain,(
    ! [A_152,B_383] :
      ( ~ r2_hidden('#skF_6'(A_152,k7_relat_1('#skF_9',B_383)),B_383)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_383))
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_152,'#skF_10')
      | r1_tarski(A_152,k7_relat_1('#skF_9',B_383))
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_395,c_2354])).

tff(c_2647,plain,(
    ! [A_385,B_386] :
      ( ~ r2_hidden('#skF_6'(A_385,k7_relat_1('#skF_9',B_386)),B_386)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_386))
      | ~ r1_tarski(A_385,'#skF_10')
      | r1_tarski(A_385,k7_relat_1('#skF_9',B_386))
      | ~ v1_relat_1(A_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2382])).

tff(c_2735,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ r1_tarski('#skF_10','#skF_10')
    | ~ v1_relat_1('#skF_10')
    | r1_tarski('#skF_10',k7_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_202,c_2647])).

tff(c_2773,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | r1_tarski('#skF_10',k7_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_2735])).

tff(c_2774,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2773])).

tff(c_2779,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_2774])).

tff(c_2783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2779])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.09  
% 5.88/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.09  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1
% 5.88/2.09  
% 5.88/2.09  %Foreground sorts:
% 5.88/2.09  
% 5.88/2.09  
% 5.88/2.09  %Background operators:
% 5.88/2.09  
% 5.88/2.09  
% 5.88/2.09  %Foreground operators:
% 5.88/2.09  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.88/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.88/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.88/2.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.88/2.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.88/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.09  tff('#skF_10', type, '#skF_10': $i).
% 5.88/2.09  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.88/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.88/2.09  tff('#skF_9', type, '#skF_9': $i).
% 5.88/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.88/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.88/2.09  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.88/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.09  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.88/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.88/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.88/2.09  
% 5.88/2.10  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 5.88/2.10  tff(f_60, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.88/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.88/2.10  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 5.88/2.10  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.88/2.10  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 5.88/2.10  tff(c_44, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.10  tff(c_32, plain, (![A_42, B_43]: (v1_relat_1(k7_relat_1(A_42, B_43)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.88/2.10  tff(c_36, plain, (~r1_tarski('#skF_10', k7_relat_1('#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.10  tff(c_42, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.88/2.10  tff(c_47, plain, (![A_51, B_52]: (~r2_hidden('#skF_1'(A_51, B_52), B_52) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.88/2.10  tff(c_52, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_47])).
% 5.88/2.10  tff(c_30, plain, (![A_25, B_35]: (r2_hidden(k4_tarski('#skF_6'(A_25, B_35), '#skF_7'(A_25, B_35)), A_25) | r1_tarski(A_25, B_35) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.10  tff(c_40, plain, (r1_tarski(k1_relat_1('#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.10  tff(c_58, plain, (![B_57, A_58]: (k7_relat_1(B_57, A_58)=B_57 | ~r1_tarski(k1_relat_1(B_57), A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.10  tff(c_65, plain, (k7_relat_1('#skF_10', '#skF_8')='#skF_10' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_40, c_58])).
% 5.88/2.10  tff(c_69, plain, (k7_relat_1('#skF_10', '#skF_8')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_65])).
% 5.88/2.10  tff(c_181, plain, (![D_87, B_88, E_89, A_90]: (r2_hidden(D_87, B_88) | ~r2_hidden(k4_tarski(D_87, E_89), k7_relat_1(A_90, B_88)) | ~v1_relat_1(k7_relat_1(A_90, B_88)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.10  tff(c_191, plain, (![D_87, E_89]: (r2_hidden(D_87, '#skF_8') | ~r2_hidden(k4_tarski(D_87, E_89), '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_181])).
% 5.88/2.10  tff(c_195, plain, (![D_91, E_92]: (r2_hidden(D_91, '#skF_8') | ~r2_hidden(k4_tarski(D_91, E_92), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_69, c_191])).
% 5.88/2.10  tff(c_199, plain, (![B_35]: (r2_hidden('#skF_6'('#skF_10', B_35), '#skF_8') | r1_tarski('#skF_10', B_35) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_195])).
% 5.88/2.10  tff(c_202, plain, (![B_35]: (r2_hidden('#skF_6'('#skF_10', B_35), '#skF_8') | r1_tarski('#skF_10', B_35))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_199])).
% 5.88/2.10  tff(c_38, plain, (r1_tarski('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.88/2.10  tff(c_100, plain, (![A_63, B_64]: (r2_hidden(k4_tarski('#skF_6'(A_63, B_64), '#skF_7'(A_63, B_64)), A_63) | r1_tarski(A_63, B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.10  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.88/2.10  tff(c_247, plain, (![A_107, B_108, B_109]: (r2_hidden(k4_tarski('#skF_6'(A_107, B_108), '#skF_7'(A_107, B_108)), B_109) | ~r1_tarski(A_107, B_109) | r1_tarski(A_107, B_108) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_100, c_2])).
% 5.88/2.10  tff(c_386, plain, (![A_152, B_153, B_154, B_155]: (r2_hidden(k4_tarski('#skF_6'(A_152, B_153), '#skF_7'(A_152, B_153)), B_154) | ~r1_tarski(B_155, B_154) | ~r1_tarski(A_152, B_155) | r1_tarski(A_152, B_153) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_247, c_2])).
% 5.88/2.10  tff(c_395, plain, (![A_152, B_153]: (r2_hidden(k4_tarski('#skF_6'(A_152, B_153), '#skF_7'(A_152, B_153)), '#skF_9') | ~r1_tarski(A_152, '#skF_10') | r1_tarski(A_152, B_153) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_38, c_386])).
% 5.88/2.10  tff(c_329, plain, (![D_134, E_135, A_136, B_137]: (r2_hidden(k4_tarski(D_134, E_135), k7_relat_1(A_136, B_137)) | ~r2_hidden(k4_tarski(D_134, E_135), A_136) | ~r2_hidden(D_134, B_137) | ~v1_relat_1(k7_relat_1(A_136, B_137)) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.10  tff(c_28, plain, (![A_25, B_35]: (~r2_hidden(k4_tarski('#skF_6'(A_25, B_35), '#skF_7'(A_25, B_35)), B_35) | r1_tarski(A_25, B_35) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.10  tff(c_2354, plain, (![A_381, A_382, B_383]: (r1_tarski(A_381, k7_relat_1(A_382, B_383)) | ~v1_relat_1(A_381) | ~r2_hidden(k4_tarski('#skF_6'(A_381, k7_relat_1(A_382, B_383)), '#skF_7'(A_381, k7_relat_1(A_382, B_383))), A_382) | ~r2_hidden('#skF_6'(A_381, k7_relat_1(A_382, B_383)), B_383) | ~v1_relat_1(k7_relat_1(A_382, B_383)) | ~v1_relat_1(A_382))), inference(resolution, [status(thm)], [c_329, c_28])).
% 5.88/2.10  tff(c_2382, plain, (![A_152, B_383]: (~r2_hidden('#skF_6'(A_152, k7_relat_1('#skF_9', B_383)), B_383) | ~v1_relat_1(k7_relat_1('#skF_9', B_383)) | ~v1_relat_1('#skF_9') | ~r1_tarski(A_152, '#skF_10') | r1_tarski(A_152, k7_relat_1('#skF_9', B_383)) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_395, c_2354])).
% 5.88/2.10  tff(c_2647, plain, (![A_385, B_386]: (~r2_hidden('#skF_6'(A_385, k7_relat_1('#skF_9', B_386)), B_386) | ~v1_relat_1(k7_relat_1('#skF_9', B_386)) | ~r1_tarski(A_385, '#skF_10') | r1_tarski(A_385, k7_relat_1('#skF_9', B_386)) | ~v1_relat_1(A_385))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2382])).
% 5.88/2.10  tff(c_2735, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~r1_tarski('#skF_10', '#skF_10') | ~v1_relat_1('#skF_10') | r1_tarski('#skF_10', k7_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_202, c_2647])).
% 5.88/2.10  tff(c_2773, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | r1_tarski('#skF_10', k7_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_2735])).
% 5.88/2.10  tff(c_2774, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_36, c_2773])).
% 5.88/2.10  tff(c_2779, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_2774])).
% 5.88/2.10  tff(c_2783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2779])).
% 5.88/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.10  
% 5.88/2.10  Inference rules
% 5.88/2.10  ----------------------
% 5.88/2.10  #Ref     : 0
% 5.88/2.10  #Sup     : 665
% 5.88/2.10  #Fact    : 0
% 5.88/2.10  #Define  : 0
% 5.88/2.10  #Split   : 16
% 5.88/2.10  #Chain   : 0
% 5.88/2.10  #Close   : 0
% 5.88/2.10  
% 5.88/2.10  Ordering : KBO
% 5.88/2.10  
% 5.88/2.10  Simplification rules
% 5.88/2.10  ----------------------
% 5.88/2.10  #Subsume      : 190
% 5.88/2.10  #Demod        : 260
% 5.88/2.10  #Tautology    : 61
% 5.88/2.10  #SimpNegUnit  : 1
% 5.88/2.10  #BackRed      : 0
% 5.88/2.10  
% 5.88/2.10  #Partial instantiations: 0
% 5.88/2.10  #Strategies tried      : 1
% 5.88/2.10  
% 5.88/2.10  Timing (in seconds)
% 5.88/2.10  ----------------------
% 5.88/2.11  Preprocessing        : 0.28
% 5.88/2.11  Parsing              : 0.15
% 5.88/2.11  CNF conversion       : 0.03
% 5.88/2.11  Main loop            : 1.06
% 5.88/2.11  Inferencing          : 0.35
% 6.00/2.11  Reduction            : 0.25
% 6.00/2.11  Demodulation         : 0.16
% 6.00/2.11  BG Simplification    : 0.03
% 6.00/2.11  Subsumption          : 0.38
% 6.00/2.11  Abstraction          : 0.04
% 6.00/2.11  MUC search           : 0.00
% 6.00/2.11  Cooper               : 0.00
% 6.00/2.11  Total                : 1.37
% 6.00/2.11  Index Insertion      : 0.00
% 6.00/2.11  Index Deletion       : 0.00
% 6.00/2.11  Index Matching       : 0.00
% 6.00/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
