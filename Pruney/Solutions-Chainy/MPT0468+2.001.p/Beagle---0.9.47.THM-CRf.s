%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 138 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,(
    ! [B_56] : k4_xboole_0(B_56,B_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_42,plain,(
    ! [A_33,B_34] :
      ( v1_relat_1(k4_xboole_0(A_33,B_34))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_123,plain,(
    ! [B_56] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_42])).

tff(c_128,plain,(
    ! [B_56] : ~ v1_relat_1(B_56) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_48])).

tff(c_137,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_117,plain,(
    ! [B_5] : k4_xboole_0(B_5,B_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_231,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_1'(A_84,B_85),'#skF_2'(A_84,B_85)),B_85)
      | r2_hidden(k4_tarski('#skF_3'(A_84,B_85),'#skF_4'(A_84,B_85)),A_84)
      | B_85 = A_84
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ! [B_37,C_38] : ~ r2_hidden(k4_tarski(B_37,C_38),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_267,plain,(
    ! [B_85] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_5',B_85),'#skF_2'('#skF_5',B_85)),B_85)
      | B_85 = '#skF_5'
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_231,c_46])).

tff(c_280,plain,(
    ! [B_85] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_5',B_85),'#skF_2'('#skF_5',B_85)),B_85)
      | B_85 = '#skF_5'
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_267])).

tff(c_281,plain,(
    ! [B_86] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_5',B_86),'#skF_2'('#skF_5',B_86)),B_86)
      | B_86 = '#skF_5'
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_267])).

tff(c_62,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_46] : k2_xboole_0(A_46,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18])).

tff(c_184,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r2_hidden(C_72,k2_xboole_0(A_74,B_73))
      | ~ r1_xboole_0(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_187,plain,(
    ! [C_72,A_46] :
      ( ~ r2_hidden(C_72,A_46)
      | ~ r2_hidden(C_72,A_46)
      | ~ r2_hidden(C_72,A_46)
      | ~ r1_xboole_0(A_46,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_184])).

tff(c_307,plain,(
    ! [B_87] :
      ( ~ r2_hidden(k4_tarski('#skF_1'('#skF_5',B_87),'#skF_2'('#skF_5',B_87)),B_87)
      | ~ r1_xboole_0(B_87,B_87)
      | B_87 = '#skF_5'
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_281,c_187])).

tff(c_320,plain,(
    ! [B_88] :
      ( ~ r1_xboole_0(B_88,B_88)
      | B_88 = '#skF_5'
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_280,c_307])).

tff(c_324,plain,(
    ! [B_13] :
      ( B_13 = '#skF_5'
      | ~ v1_relat_1(B_13)
      | k4_xboole_0(B_13,B_13) != B_13 ) ),
    inference(resolution,[status(thm)],[c_26,c_320])).

tff(c_328,plain,(
    ! [B_89] :
      ( B_89 = '#skF_5'
      | ~ v1_relat_1(B_89)
      | k1_xboole_0 != B_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_324])).

tff(c_331,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_137,c_328])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.56/1.38  
% 2.56/1.38  %Foreground sorts:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Background operators:
% 2.56/1.38  
% 2.56/1.38  
% 2.56/1.38  %Foreground operators:
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.56/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.56/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.56/1.38  
% 2.56/1.39  tff(f_87, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 2.56/1.39  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.39  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.56/1.39  tff(f_78, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.56/1.39  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.56/1.39  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 2.56/1.39  tff(f_50, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.56/1.39  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.56/1.39  tff(f_42, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 2.56/1.39  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.39  tff(c_14, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.39  tff(c_113, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.39  tff(c_118, plain, (![B_56]: (k4_xboole_0(B_56, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_113])).
% 2.56/1.39  tff(c_42, plain, (![A_33, B_34]: (v1_relat_1(k4_xboole_0(A_33, B_34)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.39  tff(c_123, plain, (![B_56]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_118, c_42])).
% 2.56/1.39  tff(c_128, plain, (![B_56]: (~v1_relat_1(B_56))), inference(splitLeft, [status(thm)], [c_123])).
% 2.56/1.39  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.39  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_48])).
% 2.56/1.39  tff(c_137, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_123])).
% 2.56/1.39  tff(c_117, plain, (![B_5]: (k4_xboole_0(B_5, B_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_113])).
% 2.56/1.39  tff(c_26, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.39  tff(c_231, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_1'(A_84, B_85), '#skF_2'(A_84, B_85)), B_85) | r2_hidden(k4_tarski('#skF_3'(A_84, B_85), '#skF_4'(A_84, B_85)), A_84) | B_85=A_84 | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.39  tff(c_46, plain, (![B_37, C_38]: (~r2_hidden(k4_tarski(B_37, C_38), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.39  tff(c_267, plain, (![B_85]: (r2_hidden(k4_tarski('#skF_1'('#skF_5', B_85), '#skF_2'('#skF_5', B_85)), B_85) | B_85='#skF_5' | ~v1_relat_1(B_85) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_231, c_46])).
% 2.56/1.39  tff(c_280, plain, (![B_85]: (r2_hidden(k4_tarski('#skF_1'('#skF_5', B_85), '#skF_2'('#skF_5', B_85)), B_85) | B_85='#skF_5' | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_267])).
% 2.56/1.39  tff(c_281, plain, (![B_86]: (r2_hidden(k4_tarski('#skF_1'('#skF_5', B_86), '#skF_2'('#skF_5', B_86)), B_86) | B_86='#skF_5' | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_267])).
% 2.56/1.39  tff(c_62, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k2_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.56/1.39  tff(c_18, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.39  tff(c_68, plain, (![A_46]: (k2_xboole_0(A_46, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_62, c_18])).
% 2.56/1.39  tff(c_184, plain, (![C_72, B_73, A_74]: (~r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r2_hidden(C_72, k2_xboole_0(A_74, B_73)) | ~r1_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.39  tff(c_187, plain, (![C_72, A_46]: (~r2_hidden(C_72, A_46) | ~r2_hidden(C_72, A_46) | ~r2_hidden(C_72, A_46) | ~r1_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_68, c_184])).
% 2.56/1.39  tff(c_307, plain, (![B_87]: (~r2_hidden(k4_tarski('#skF_1'('#skF_5', B_87), '#skF_2'('#skF_5', B_87)), B_87) | ~r1_xboole_0(B_87, B_87) | B_87='#skF_5' | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_281, c_187])).
% 2.56/1.39  tff(c_320, plain, (![B_88]: (~r1_xboole_0(B_88, B_88) | B_88='#skF_5' | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_280, c_307])).
% 2.56/1.39  tff(c_324, plain, (![B_13]: (B_13='#skF_5' | ~v1_relat_1(B_13) | k4_xboole_0(B_13, B_13)!=B_13)), inference(resolution, [status(thm)], [c_26, c_320])).
% 2.56/1.39  tff(c_328, plain, (![B_89]: (B_89='#skF_5' | ~v1_relat_1(B_89) | k1_xboole_0!=B_89)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_324])).
% 2.56/1.39  tff(c_331, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_137, c_328])).
% 2.56/1.39  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_331])).
% 2.56/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  Inference rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Ref     : 0
% 2.56/1.39  #Sup     : 59
% 2.56/1.39  #Fact    : 0
% 2.56/1.39  #Define  : 0
% 2.56/1.39  #Split   : 1
% 2.56/1.39  #Chain   : 0
% 2.56/1.39  #Close   : 0
% 2.56/1.39  
% 2.56/1.39  Ordering : KBO
% 2.56/1.39  
% 2.56/1.39  Simplification rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Subsume      : 5
% 2.56/1.39  #Demod        : 13
% 2.56/1.39  #Tautology    : 30
% 2.56/1.39  #SimpNegUnit  : 4
% 2.56/1.39  #BackRed      : 1
% 2.56/1.39  
% 2.56/1.39  #Partial instantiations: 0
% 2.56/1.39  #Strategies tried      : 1
% 2.56/1.39  
% 2.56/1.39  Timing (in seconds)
% 2.56/1.39  ----------------------
% 2.56/1.39  Preprocessing        : 0.33
% 2.56/1.40  Parsing              : 0.18
% 2.56/1.40  CNF conversion       : 0.02
% 2.56/1.40  Main loop            : 0.23
% 2.56/1.40  Inferencing          : 0.08
% 2.56/1.40  Reduction            : 0.07
% 2.56/1.40  Demodulation         : 0.05
% 2.56/1.40  BG Simplification    : 0.02
% 2.56/1.40  Subsumption          : 0.04
% 2.56/1.40  Abstraction          : 0.01
% 2.56/1.40  MUC search           : 0.00
% 2.56/1.40  Cooper               : 0.00
% 2.56/1.40  Total                : 0.59
% 2.56/1.40  Index Insertion      : 0.00
% 2.56/1.40  Index Deletion       : 0.00
% 2.56/1.40  Index Matching       : 0.00
% 2.56/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
