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
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 107 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
                & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_172,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(k1_relat_1(A_71),k1_relat_1(B_72)) = k1_relat_1(k2_xboole_0(A_71,B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_relat_1(A_73),k1_relat_1(k2_xboole_0(A_73,B_74)))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_10])).

tff(c_218,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_200])).

tff(c_223,plain,(
    r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_218])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_223])).

tff(c_226,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_351,plain,(
    ! [A_96,C_97] :
      ( r2_hidden(k4_tarski('#skF_5'(A_96,k2_relat_1(A_96),C_97),C_97),A_96)
      | ~ r2_hidden(C_97,k2_relat_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1242,plain,(
    ! [A_168,C_169,B_170] :
      ( r2_hidden(k4_tarski('#skF_5'(A_168,k2_relat_1(A_168),C_169),C_169),B_170)
      | ~ r1_tarski(A_168,B_170)
      | ~ r2_hidden(C_169,k2_relat_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_351,c_2])).

tff(c_20,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k2_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(D_33,C_30),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2402,plain,(
    ! [C_237,B_238,A_239] :
      ( r2_hidden(C_237,k2_relat_1(B_238))
      | ~ r1_tarski(A_239,B_238)
      | ~ r2_hidden(C_237,k2_relat_1(A_239)) ) ),
    inference(resolution,[status(thm)],[c_1242,c_20])).

tff(c_2472,plain,(
    ! [C_240] :
      ( r2_hidden(C_240,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_240,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2402])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2911,plain,(
    ! [A_254] :
      ( r1_tarski(A_254,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_254,k2_relat_1('#skF_7')),k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2472,c_4])).

tff(c_2923,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_2911])).

tff(c_2929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_226,c_2923])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.85  
% 4.41/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.85  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 4.41/1.85  
% 4.41/1.85  %Foreground sorts:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Background operators:
% 4.41/1.85  
% 4.41/1.85  
% 4.41/1.85  %Foreground operators:
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.41/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.41/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.41/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.41/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.41/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.41/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.41/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.41/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.41/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.41/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.85  
% 4.41/1.87  tff(f_76, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.41/1.87  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.41/1.87  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 4.41/1.87  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.41/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.41/1.87  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.41/1.87  tff(c_32, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.41/1.87  tff(c_64, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_32])).
% 4.41/1.87  tff(c_38, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.41/1.87  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.41/1.87  tff(c_34, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.41/1.87  tff(c_40, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.41/1.87  tff(c_48, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_34, c_40])).
% 4.41/1.87  tff(c_172, plain, (![A_71, B_72]: (k2_xboole_0(k1_relat_1(A_71), k1_relat_1(B_72))=k1_relat_1(k2_xboole_0(A_71, B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.87  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.41/1.87  tff(c_200, plain, (![A_73, B_74]: (r1_tarski(k1_relat_1(A_73), k1_relat_1(k2_xboole_0(A_73, B_74))) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_172, c_10])).
% 4.41/1.87  tff(c_218, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_48, c_200])).
% 4.41/1.87  tff(c_223, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_218])).
% 4.41/1.87  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_223])).
% 4.41/1.87  tff(c_226, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_32])).
% 4.41/1.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.41/1.87  tff(c_351, plain, (![A_96, C_97]: (r2_hidden(k4_tarski('#skF_5'(A_96, k2_relat_1(A_96), C_97), C_97), A_96) | ~r2_hidden(C_97, k2_relat_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.41/1.87  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.41/1.87  tff(c_1242, plain, (![A_168, C_169, B_170]: (r2_hidden(k4_tarski('#skF_5'(A_168, k2_relat_1(A_168), C_169), C_169), B_170) | ~r1_tarski(A_168, B_170) | ~r2_hidden(C_169, k2_relat_1(A_168)))), inference(resolution, [status(thm)], [c_351, c_2])).
% 4.41/1.87  tff(c_20, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k2_relat_1(A_15)) | ~r2_hidden(k4_tarski(D_33, C_30), A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.41/1.87  tff(c_2402, plain, (![C_237, B_238, A_239]: (r2_hidden(C_237, k2_relat_1(B_238)) | ~r1_tarski(A_239, B_238) | ~r2_hidden(C_237, k2_relat_1(A_239)))), inference(resolution, [status(thm)], [c_1242, c_20])).
% 4.41/1.87  tff(c_2472, plain, (![C_240]: (r2_hidden(C_240, k2_relat_1('#skF_7')) | ~r2_hidden(C_240, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_34, c_2402])).
% 4.41/1.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.41/1.87  tff(c_2911, plain, (![A_254]: (r1_tarski(A_254, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_254, k2_relat_1('#skF_7')), k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_2472, c_4])).
% 4.41/1.87  tff(c_2923, plain, (r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_2911])).
% 4.41/1.87  tff(c_2929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_226, c_2923])).
% 4.41/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.87  
% 4.41/1.87  Inference rules
% 4.41/1.87  ----------------------
% 4.41/1.87  #Ref     : 0
% 4.41/1.87  #Sup     : 715
% 4.41/1.87  #Fact    : 0
% 4.41/1.87  #Define  : 0
% 4.41/1.87  #Split   : 5
% 4.41/1.87  #Chain   : 0
% 4.41/1.87  #Close   : 0
% 4.41/1.87  
% 4.41/1.87  Ordering : KBO
% 4.41/1.87  
% 4.41/1.87  Simplification rules
% 4.41/1.87  ----------------------
% 4.41/1.87  #Subsume      : 169
% 4.41/1.87  #Demod        : 208
% 4.41/1.87  #Tautology    : 173
% 4.41/1.87  #SimpNegUnit  : 2
% 4.41/1.87  #BackRed      : 0
% 4.41/1.87  
% 4.41/1.87  #Partial instantiations: 0
% 4.41/1.87  #Strategies tried      : 1
% 4.41/1.87  
% 4.41/1.87  Timing (in seconds)
% 4.41/1.87  ----------------------
% 4.41/1.87  Preprocessing        : 0.32
% 4.41/1.87  Parsing              : 0.17
% 4.41/1.87  CNF conversion       : 0.03
% 4.41/1.87  Main loop            : 0.71
% 4.41/1.87  Inferencing          : 0.25
% 4.41/1.87  Reduction            : 0.21
% 4.41/1.87  Demodulation         : 0.15
% 4.41/1.87  BG Simplification    : 0.03
% 4.41/1.87  Subsumption          : 0.18
% 4.41/1.87  Abstraction          : 0.03
% 4.41/1.87  MUC search           : 0.00
% 4.41/1.87  Cooper               : 0.00
% 4.41/1.87  Total                : 1.06
% 4.41/1.87  Index Insertion      : 0.00
% 4.41/1.87  Index Deletion       : 0.00
% 4.41/1.87  Index Matching       : 0.00
% 4.41/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
