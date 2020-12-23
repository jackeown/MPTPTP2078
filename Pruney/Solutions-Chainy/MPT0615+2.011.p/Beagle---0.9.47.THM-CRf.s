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
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 154 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_1'(A_19,B_20),B_20)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_28,B_29,B_30] :
      ( r2_hidden('#skF_1'(A_28,B_29),B_30)
      | ~ r1_tarski(A_28,B_30)
      | r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_34,B_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski(A_34,B_37)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_89,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),k7_relat_1('#skF_3',k1_relat_1('#skF_2')))
      | ~ r1_tarski(A_38,'#skF_2')
      | r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_33,c_76])).

tff(c_135,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_46)
      | ~ r1_tarski(k7_relat_1('#skF_3',k1_relat_1('#skF_2')),B_46)
      | ~ r1_tarski(A_44,'#skF_2')
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_150,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),'#skF_3')
      | ~ r1_tarski(A_44,'#skF_2')
      | r1_tarski(A_44,B_45)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_162,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),'#skF_3')
      | ~ r1_tarski(A_47,'#skF_2')
      | r1_tarski(A_47,B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_171,plain,(
    ! [A_49] :
      ( ~ r1_tarski(A_49,'#skF_2')
      | r1_tarski(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_179,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_179])).

tff(c_191,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_200,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ r1_tarski(k1_relat_1(B_54),A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_205,plain,(
    ! [B_54] :
      ( k7_relat_1(B_54,k1_relat_1(B_54)) = B_54
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_32,c_200])).

tff(c_219,plain,(
    ! [B_57,A_58,C_59] :
      ( r1_tarski(k7_relat_1(B_57,A_58),k7_relat_1(C_59,A_58))
      | ~ r1_tarski(B_57,C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_511,plain,(
    ! [B_103,C_104] :
      ( r1_tarski(B_103,k7_relat_1(C_104,k1_relat_1(B_103)))
      | ~ r1_tarski(B_103,C_104)
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_219])).

tff(c_192,plain,(
    ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_532,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_511,c_192])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_191,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.35  
% 2.53/1.35  %Foreground sorts:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Background operators:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Foreground operators:
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.35  
% 2.71/1.37  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 2.71/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.37  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.71/1.37  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.71/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 2.71/1.37  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.37  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.37  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.37  tff(c_33, plain, (r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_24])).
% 2.71/1.37  tff(c_18, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.37  tff(c_40, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_18])).
% 2.71/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_27, plain, (![A_19, B_20]: (~r2_hidden('#skF_1'(A_19, B_20), B_20) | r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_32, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_27])).
% 2.71/1.37  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.37  tff(c_35, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_60, plain, (![A_28, B_29, B_30]: (r2_hidden('#skF_1'(A_28, B_29), B_30) | ~r1_tarski(A_28, B_30) | r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.71/1.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_76, plain, (![A_34, B_35, B_36, B_37]: (r2_hidden('#skF_1'(A_34, B_35), B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski(A_34, B_37) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.71/1.37  tff(c_89, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), k7_relat_1('#skF_3', k1_relat_1('#skF_2'))) | ~r1_tarski(A_38, '#skF_2') | r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_33, c_76])).
% 2.71/1.37  tff(c_135, plain, (![A_44, B_45, B_46]: (r2_hidden('#skF_1'(A_44, B_45), B_46) | ~r1_tarski(k7_relat_1('#skF_3', k1_relat_1('#skF_2')), B_46) | ~r1_tarski(A_44, '#skF_2') | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.71/1.37  tff(c_150, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), '#skF_3') | ~r1_tarski(A_44, '#skF_2') | r1_tarski(A_44, B_45) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_135])).
% 2.71/1.37  tff(c_162, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), '#skF_3') | ~r1_tarski(A_47, '#skF_2') | r1_tarski(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 2.71/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.37  tff(c_171, plain, (![A_49]: (~r1_tarski(A_49, '#skF_2') | r1_tarski(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_162, c_4])).
% 2.71/1.37  tff(c_179, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.71/1.37  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_179])).
% 2.71/1.37  tff(c_191, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 2.71/1.37  tff(c_200, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~r1_tarski(k1_relat_1(B_54), A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.37  tff(c_205, plain, (![B_54]: (k7_relat_1(B_54, k1_relat_1(B_54))=B_54 | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_32, c_200])).
% 2.71/1.37  tff(c_219, plain, (![B_57, A_58, C_59]: (r1_tarski(k7_relat_1(B_57, A_58), k7_relat_1(C_59, A_58)) | ~r1_tarski(B_57, C_59) | ~v1_relat_1(C_59) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.37  tff(c_511, plain, (![B_103, C_104]: (r1_tarski(B_103, k7_relat_1(C_104, k1_relat_1(B_103))) | ~r1_tarski(B_103, C_104) | ~v1_relat_1(C_104) | ~v1_relat_1(B_103) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_205, c_219])).
% 2.71/1.37  tff(c_192, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_24])).
% 2.71/1.37  tff(c_532, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_511, c_192])).
% 2.71/1.37  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_191, c_532])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 119
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 1
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 25
% 2.71/1.37  #Demod        : 36
% 2.71/1.37  #Tautology    : 22
% 2.71/1.37  #SimpNegUnit  : 1
% 2.71/1.37  #BackRed      : 0
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.27
% 2.71/1.37  Parsing              : 0.15
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.33
% 2.71/1.37  Inferencing          : 0.13
% 2.71/1.37  Reduction            : 0.08
% 2.71/1.37  Demodulation         : 0.06
% 2.71/1.37  BG Simplification    : 0.01
% 2.71/1.37  Subsumption          : 0.08
% 2.71/1.37  Abstraction          : 0.01
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.63
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
