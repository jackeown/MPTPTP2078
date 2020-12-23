%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 133 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 388 expanded)
%              Number of equality atoms :    8 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(c_22,plain,(
    k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    r2_hidden('#skF_2',k1_relat_1(k8_relat_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_39,C_40] :
      ( r2_hidden(k4_tarski(A_39,k1_funct_1(C_40,A_39)),C_40)
      | ~ r2_hidden(A_39,k1_relat_1(C_40))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(k4_tarski(A_59,k1_funct_1(C_60,A_59)),B_61)
      | ~ r1_tarski(C_60,B_61)
      | ~ r2_hidden(A_59,k1_relat_1(C_60))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_20,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_hidden(A_12,k1_relat_1(C_14))
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden(A_67,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ r1_tarski(C_69,B_68)
      | ~ r2_hidden(A_67,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_199,plain,(
    ! [A_87,B_88,A_89] :
      ( r2_hidden(A_87,k1_relat_1(B_88))
      | ~ v1_funct_1(B_88)
      | ~ r2_hidden(A_87,k1_relat_1(k8_relat_1(A_89,B_88)))
      | ~ v1_funct_1(k8_relat_1(A_89,B_88))
      | ~ v1_relat_1(k8_relat_1(A_89,B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_226,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k8_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_199])).

tff(c_235,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k8_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_226])).

tff(c_236,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_239,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_239])).

tff(c_245,plain,(
    v1_relat_1(k8_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k8_relat_1(A_10,B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_244,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_3','#skF_4'))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_246,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_249,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_246])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_249])).

tff(c_255,plain,(
    v1_funct_1(k8_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_18,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_funct_1(C_14,A_12) = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [C_75,A_76,B_77] :
      ( k1_funct_1(C_75,A_76) = k1_funct_1(B_77,A_76)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ r1_tarski(C_75,B_77)
      | ~ r2_hidden(A_76,k1_relat_1(C_75))
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_120,c_18])).

tff(c_359,plain,(
    ! [A_113,B_114,A_115] :
      ( k1_funct_1(k8_relat_1(A_113,B_114),A_115) = k1_funct_1(B_114,A_115)
      | ~ v1_funct_1(B_114)
      | ~ r2_hidden(A_115,k1_relat_1(k8_relat_1(A_113,B_114)))
      | ~ v1_funct_1(k8_relat_1(A_113,B_114))
      | ~ v1_relat_1(k8_relat_1(A_113,B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_390,plain,
    ( k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k8_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_359])).

tff(c_400,plain,(
    k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_245,c_255,c_26,c_390])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.33  
% 2.49/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.33  
% 2.49/1.33  %Foreground sorts:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Background operators:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Foreground operators:
% 2.49/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.49/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.33  
% 2.49/1.34  tff(f_67, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 2.49/1.34  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.49/1.34  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.49/1.34  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.49/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.34  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.49/1.34  tff(c_22, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.34  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.34  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.34  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.34  tff(c_24, plain, (r2_hidden('#skF_2', k1_relat_1(k8_relat_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.34  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.34  tff(c_65, plain, (![A_39, C_40]: (r2_hidden(k4_tarski(A_39, k1_funct_1(C_40, A_39)), C_40) | ~r2_hidden(A_39, k1_relat_1(C_40)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.34  tff(c_120, plain, (![A_59, C_60, B_61]: (r2_hidden(k4_tarski(A_59, k1_funct_1(C_60, A_59)), B_61) | ~r1_tarski(C_60, B_61) | ~r2_hidden(A_59, k1_relat_1(C_60)) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.49/1.34  tff(c_20, plain, (![A_12, C_14, B_13]: (r2_hidden(A_12, k1_relat_1(C_14)) | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.34  tff(c_145, plain, (![A_67, B_68, C_69]: (r2_hidden(A_67, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~r1_tarski(C_69, B_68) | ~r2_hidden(A_67, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_120, c_20])).
% 2.49/1.34  tff(c_199, plain, (![A_87, B_88, A_89]: (r2_hidden(A_87, k1_relat_1(B_88)) | ~v1_funct_1(B_88) | ~r2_hidden(A_87, k1_relat_1(k8_relat_1(A_89, B_88))) | ~v1_funct_1(k8_relat_1(A_89, B_88)) | ~v1_relat_1(k8_relat_1(A_89, B_88)) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_10, c_145])).
% 2.49/1.34  tff(c_226, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_funct_1(k8_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_199])).
% 2.49/1.34  tff(c_235, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1(k8_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_226])).
% 2.49/1.34  tff(c_236, plain, (~v1_relat_1(k8_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_235])).
% 2.49/1.34  tff(c_239, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_236])).
% 2.49/1.34  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_239])).
% 2.49/1.34  tff(c_245, plain, (v1_relat_1(k8_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_235])).
% 2.49/1.34  tff(c_12, plain, (![A_10, B_11]: (v1_funct_1(k8_relat_1(A_10, B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.34  tff(c_244, plain, (~v1_funct_1(k8_relat_1('#skF_3', '#skF_4')) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_235])).
% 2.49/1.34  tff(c_246, plain, (~v1_funct_1(k8_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_244])).
% 2.49/1.34  tff(c_249, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_246])).
% 2.49/1.34  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_249])).
% 2.49/1.34  tff(c_255, plain, (v1_funct_1(k8_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_244])).
% 2.49/1.34  tff(c_18, plain, (![C_14, A_12, B_13]: (k1_funct_1(C_14, A_12)=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.34  tff(c_165, plain, (![C_75, A_76, B_77]: (k1_funct_1(C_75, A_76)=k1_funct_1(B_77, A_76) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77) | ~r1_tarski(C_75, B_77) | ~r2_hidden(A_76, k1_relat_1(C_75)) | ~v1_funct_1(C_75) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_120, c_18])).
% 2.49/1.34  tff(c_359, plain, (![A_113, B_114, A_115]: (k1_funct_1(k8_relat_1(A_113, B_114), A_115)=k1_funct_1(B_114, A_115) | ~v1_funct_1(B_114) | ~r2_hidden(A_115, k1_relat_1(k8_relat_1(A_113, B_114))) | ~v1_funct_1(k8_relat_1(A_113, B_114)) | ~v1_relat_1(k8_relat_1(A_113, B_114)) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.49/1.34  tff(c_390, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_funct_1(k8_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_359])).
% 2.49/1.34  tff(c_400, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_245, c_255, c_26, c_390])).
% 2.49/1.34  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_400])).
% 2.49/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  Inference rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Ref     : 0
% 2.49/1.34  #Sup     : 82
% 2.49/1.34  #Fact    : 0
% 2.49/1.34  #Define  : 0
% 2.49/1.34  #Split   : 2
% 2.49/1.34  #Chain   : 0
% 2.49/1.34  #Close   : 0
% 2.49/1.34  
% 2.49/1.34  Ordering : KBO
% 2.49/1.34  
% 2.49/1.34  Simplification rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Subsume      : 10
% 2.49/1.34  #Demod        : 11
% 2.49/1.34  #Tautology    : 7
% 2.49/1.34  #SimpNegUnit  : 1
% 2.49/1.34  #BackRed      : 0
% 2.49/1.34  
% 2.49/1.34  #Partial instantiations: 0
% 2.49/1.34  #Strategies tried      : 1
% 2.49/1.34  
% 2.49/1.34  Timing (in seconds)
% 2.49/1.34  ----------------------
% 2.49/1.35  Preprocessing        : 0.27
% 2.49/1.35  Parsing              : 0.15
% 2.49/1.35  CNF conversion       : 0.02
% 2.49/1.35  Main loop            : 0.31
% 2.49/1.35  Inferencing          : 0.12
% 2.49/1.35  Reduction            : 0.07
% 2.49/1.35  Demodulation         : 0.05
% 2.49/1.35  BG Simplification    : 0.02
% 2.49/1.35  Subsumption          : 0.09
% 2.49/1.35  Abstraction          : 0.01
% 2.49/1.35  MUC search           : 0.00
% 2.49/1.35  Cooper               : 0.00
% 2.49/1.35  Total                : 0.61
% 2.49/1.35  Index Insertion      : 0.00
% 2.49/1.35  Index Deletion       : 0.00
% 2.49/1.35  Index Matching       : 0.00
% 2.49/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
