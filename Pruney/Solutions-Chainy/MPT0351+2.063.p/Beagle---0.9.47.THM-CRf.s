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
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  94 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 115 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_37,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_159,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_197,plain,(
    ! [A_74,B_75] :
      ( k4_subset_1(A_74,B_75,A_74) = k2_xboole_0(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_37,c_159])).

tff(c_204,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_34,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_34])).

tff(c_221,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_38])).

tff(c_178,plain,(
    ! [B_73] :
      ( k4_subset_1('#skF_2',B_73,'#skF_3') = k2_xboole_0(B_73,'#skF_3')
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_159])).

tff(c_186,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_178])).

tff(c_205,plain,(
    ! [A_76,C_77,B_78] :
      ( k4_subset_1(A_76,C_77,B_78) = k4_subset_1(A_76,B_78,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_226,plain,(
    ! [B_80] :
      ( k4_subset_1('#skF_2',B_80,'#skF_3') = k4_subset_1('#skF_2','#skF_3',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_230,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k4_subset_1('#skF_2','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_226])).

tff(c_235,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_186,c_230])).

tff(c_12,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_256,plain,(
    ! [A_83,B_84,A_85] :
      ( r2_hidden('#skF_1'(A_83,B_84),A_85)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_85))
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_268,plain,(
    ! [A_86,A_87] :
      ( ~ m1_subset_1(A_86,k1_zfmisc_1(A_87))
      | r1_tarski(A_86,A_87) ) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_277,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_268])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_291,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_277,c_10])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_295,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_14])).

tff(c_298,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_12,c_295])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.37  
% 2.22/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.38  
% 2.22/1.38  %Foreground sorts:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Background operators:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Foreground operators:
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.22/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.22/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.38  
% 2.22/1.39  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.22/1.39  tff(f_56, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.22/1.39  tff(f_58, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.22/1.39  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.22/1.39  tff(f_54, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.22/1.39  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.22/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.22/1.39  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.22/1.39  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.22/1.39  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.22/1.39  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.39  tff(c_26, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.39  tff(c_28, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.22/1.39  tff(c_37, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.22/1.39  tff(c_159, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.39  tff(c_197, plain, (![A_74, B_75]: (k4_subset_1(A_74, B_75, A_74)=k2_xboole_0(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_37, c_159])).
% 2.22/1.39  tff(c_204, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_197])).
% 2.22/1.39  tff(c_34, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.39  tff(c_38, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_34])).
% 2.22/1.39  tff(c_221, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_38])).
% 2.22/1.39  tff(c_178, plain, (![B_73]: (k4_subset_1('#skF_2', B_73, '#skF_3')=k2_xboole_0(B_73, '#skF_3') | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_159])).
% 2.22/1.39  tff(c_186, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_37, c_178])).
% 2.22/1.39  tff(c_205, plain, (![A_76, C_77, B_78]: (k4_subset_1(A_76, C_77, B_78)=k4_subset_1(A_76, B_78, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.22/1.39  tff(c_226, plain, (![B_80]: (k4_subset_1('#skF_2', B_80, '#skF_3')=k4_subset_1('#skF_2', '#skF_3', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_205])).
% 2.22/1.39  tff(c_230, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k4_subset_1('#skF_2', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_37, c_226])).
% 2.22/1.39  tff(c_235, plain, (k2_xboole_0('#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_186, c_230])).
% 2.22/1.39  tff(c_12, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.39  tff(c_146, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.39  tff(c_256, plain, (![A_83, B_84, A_85]: (r2_hidden('#skF_1'(A_83, B_84), A_85) | ~m1_subset_1(A_83, k1_zfmisc_1(A_85)) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_6, c_146])).
% 2.22/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.39  tff(c_268, plain, (![A_86, A_87]: (~m1_subset_1(A_86, k1_zfmisc_1(A_87)) | r1_tarski(A_86, A_87))), inference(resolution, [status(thm)], [c_256, c_4])).
% 2.22/1.39  tff(c_277, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_268])).
% 2.22/1.39  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.39  tff(c_291, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_277, c_10])).
% 2.22/1.39  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.39  tff(c_295, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_291, c_14])).
% 2.22/1.39  tff(c_298, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_12, c_295])).
% 2.22/1.39  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_298])).
% 2.22/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.39  
% 2.22/1.39  Inference rules
% 2.22/1.39  ----------------------
% 2.22/1.39  #Ref     : 0
% 2.22/1.39  #Sup     : 65
% 2.22/1.39  #Fact    : 0
% 2.22/1.39  #Define  : 0
% 2.22/1.39  #Split   : 0
% 2.22/1.39  #Chain   : 0
% 2.22/1.39  #Close   : 0
% 2.22/1.39  
% 2.22/1.39  Ordering : KBO
% 2.22/1.39  
% 2.22/1.39  Simplification rules
% 2.22/1.39  ----------------------
% 2.22/1.39  #Subsume      : 1
% 2.22/1.39  #Demod        : 19
% 2.22/1.39  #Tautology    : 39
% 2.22/1.39  #SimpNegUnit  : 1
% 2.22/1.39  #BackRed      : 2
% 2.22/1.39  
% 2.22/1.39  #Partial instantiations: 0
% 2.22/1.39  #Strategies tried      : 1
% 2.22/1.39  
% 2.22/1.39  Timing (in seconds)
% 2.22/1.39  ----------------------
% 2.22/1.39  Preprocessing        : 0.35
% 2.22/1.39  Parsing              : 0.19
% 2.22/1.39  CNF conversion       : 0.02
% 2.22/1.39  Main loop            : 0.21
% 2.22/1.39  Inferencing          : 0.08
% 2.49/1.39  Reduction            : 0.06
% 2.49/1.39  Demodulation         : 0.05
% 2.49/1.39  BG Simplification    : 0.01
% 2.49/1.39  Subsumption          : 0.04
% 2.49/1.39  Abstraction          : 0.01
% 2.49/1.39  MUC search           : 0.00
% 2.49/1.39  Cooper               : 0.00
% 2.49/1.39  Total                : 0.59
% 2.49/1.39  Index Insertion      : 0.00
% 2.49/1.39  Index Deletion       : 0.00
% 2.49/1.39  Index Matching       : 0.00
% 2.49/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
