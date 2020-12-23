%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  85 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 158 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4'))
    | ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_36])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( k9_relat_1(A_6,k1_tarski(B_8)) = k11_relat_1(A_6,B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_3'(A_39,B_40,C_41),B_40)
      | ~ r2_hidden(A_39,k9_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_47,A_48,C_49] :
      ( '#skF_3'(A_47,k1_tarski(A_48),C_49) = A_48
      | ~ r2_hidden(A_47,k9_relat_1(C_49,k1_tarski(A_48)))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_222,plain,(
    ! [A_61,B_62,A_63] :
      ( '#skF_3'(A_61,k1_tarski(B_62),A_63) = B_62
      | ~ r2_hidden(A_61,k11_relat_1(A_63,B_62))
      | ~ v1_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_241,plain,
    ( '#skF_3'('#skF_5',k1_tarski('#skF_4'),'#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_222])).

tff(c_248,plain,(
    '#skF_3'('#skF_5',k1_tarski('#skF_4'),'#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_241])).

tff(c_20,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k4_tarski('#skF_3'(A_9,B_10,C_11),A_9),C_11)
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_252,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k9_relat_1('#skF_6',k1_tarski('#skF_4')))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_20])).

tff(c_262,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k9_relat_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_252])).

tff(c_263,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_262])).

tff(c_302,plain,
    ( ~ r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_263])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54,c_302])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_307,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_323,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(A_73,k1_relat_1(C_74))
      | ~ r2_hidden(k4_tarski(A_73,B_75),C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_323])).

tff(c_333,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_326])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_438,plain,(
    ! [A_100,C_101,B_102,D_103] :
      ( r2_hidden(A_100,k9_relat_1(C_101,B_102))
      | ~ r2_hidden(D_103,B_102)
      | ~ r2_hidden(k4_tarski(D_103,A_100),C_101)
      | ~ r2_hidden(D_103,k1_relat_1(C_101))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_575,plain,(
    ! [A_120,C_121,C_122] :
      ( r2_hidden(A_120,k9_relat_1(C_121,k1_tarski(C_122)))
      | ~ r2_hidden(k4_tarski(C_122,A_120),C_121)
      | ~ r2_hidden(C_122,k1_relat_1(C_121))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_4,c_438])).

tff(c_772,plain,(
    ! [A_134,A_135,B_136] :
      ( r2_hidden(A_134,k11_relat_1(A_135,B_136))
      | ~ r2_hidden(k4_tarski(B_136,A_134),A_135)
      | ~ r2_hidden(B_136,k1_relat_1(A_135))
      | ~ v1_relat_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_575])).

tff(c_798,plain,
    ( r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4'))
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_772])).

tff(c_811,plain,(
    r2_hidden('#skF_5',k11_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_333,c_798])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.46  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.46  
% 3.06/1.47  tff(f_63, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.06/1.47  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.06/1.47  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.06/1.47  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.06/1.47  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.06/1.47  tff(c_28, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.47  tff(c_30, plain, (~r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4')) | ~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.47  tff(c_53, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 3.06/1.47  tff(c_36, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.47  tff(c_54, plain, (r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_53, c_36])).
% 3.06/1.47  tff(c_14, plain, (![A_6, B_8]: (k9_relat_1(A_6, k1_tarski(B_8))=k11_relat_1(A_6, B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.47  tff(c_97, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_3'(A_39, B_40, C_41), B_40) | ~r2_hidden(A_39, k9_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.47  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.47  tff(c_110, plain, (![A_47, A_48, C_49]: ('#skF_3'(A_47, k1_tarski(A_48), C_49)=A_48 | ~r2_hidden(A_47, k9_relat_1(C_49, k1_tarski(A_48))) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_97, c_2])).
% 3.06/1.47  tff(c_222, plain, (![A_61, B_62, A_63]: ('#skF_3'(A_61, k1_tarski(B_62), A_63)=B_62 | ~r2_hidden(A_61, k11_relat_1(A_63, B_62)) | ~v1_relat_1(A_63) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 3.06/1.47  tff(c_241, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_4'), '#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_222])).
% 3.06/1.47  tff(c_248, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_4'), '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_241])).
% 3.06/1.47  tff(c_20, plain, (![A_9, B_10, C_11]: (r2_hidden(k4_tarski('#skF_3'(A_9, B_10, C_11), A_9), C_11) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.47  tff(c_252, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k9_relat_1('#skF_6', k1_tarski('#skF_4'))) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_248, c_20])).
% 3.06/1.47  tff(c_262, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k9_relat_1('#skF_6', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_252])).
% 3.06/1.47  tff(c_263, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_6', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_53, c_262])).
% 3.06/1.47  tff(c_302, plain, (~r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_14, c_263])).
% 3.06/1.47  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_54, c_302])).
% 3.06/1.47  tff(c_306, plain, (~r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4'))), inference(splitRight, [status(thm)], [c_30])).
% 3.06/1.47  tff(c_307, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 3.06/1.47  tff(c_323, plain, (![A_73, C_74, B_75]: (r2_hidden(A_73, k1_relat_1(C_74)) | ~r2_hidden(k4_tarski(A_73, B_75), C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.47  tff(c_326, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_307, c_323])).
% 3.06/1.47  tff(c_333, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_326])).
% 3.06/1.47  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.47  tff(c_438, plain, (![A_100, C_101, B_102, D_103]: (r2_hidden(A_100, k9_relat_1(C_101, B_102)) | ~r2_hidden(D_103, B_102) | ~r2_hidden(k4_tarski(D_103, A_100), C_101) | ~r2_hidden(D_103, k1_relat_1(C_101)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.47  tff(c_575, plain, (![A_120, C_121, C_122]: (r2_hidden(A_120, k9_relat_1(C_121, k1_tarski(C_122))) | ~r2_hidden(k4_tarski(C_122, A_120), C_121) | ~r2_hidden(C_122, k1_relat_1(C_121)) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_4, c_438])).
% 3.06/1.47  tff(c_772, plain, (![A_134, A_135, B_136]: (r2_hidden(A_134, k11_relat_1(A_135, B_136)) | ~r2_hidden(k4_tarski(B_136, A_134), A_135) | ~r2_hidden(B_136, k1_relat_1(A_135)) | ~v1_relat_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_14, c_575])).
% 3.06/1.47  tff(c_798, plain, (r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4')) | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_307, c_772])).
% 3.06/1.47  tff(c_811, plain, (r2_hidden('#skF_5', k11_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_333, c_798])).
% 3.06/1.47  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_811])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 163
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 1
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 5
% 3.06/1.47  #Demod        : 25
% 3.06/1.47  #Tautology    : 24
% 3.06/1.47  #SimpNegUnit  : 4
% 3.06/1.47  #BackRed      : 0
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.48  Preprocessing        : 0.30
% 3.06/1.48  Parsing              : 0.16
% 3.06/1.48  CNF conversion       : 0.02
% 3.06/1.48  Main loop            : 0.42
% 3.06/1.48  Inferencing          : 0.16
% 3.06/1.48  Reduction            : 0.11
% 3.06/1.48  Demodulation         : 0.07
% 3.06/1.48  BG Simplification    : 0.03
% 3.06/1.48  Subsumption          : 0.09
% 3.06/1.48  Abstraction          : 0.03
% 3.06/1.48  MUC search           : 0.00
% 3.06/1.48  Cooper               : 0.00
% 3.06/1.48  Total                : 0.75
% 3.06/1.48  Index Insertion      : 0.00
% 3.06/1.48  Index Deletion       : 0.00
% 3.06/1.48  Index Matching       : 0.00
% 3.06/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
