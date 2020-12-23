%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  68 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_25] : m1_subset_1(k2_subset_1(A_25),k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_45,plain,(
    ! [A_25] : m1_subset_1(A_25,k1_zfmisc_1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_526,plain,(
    ! [A_101,B_102,C_103] :
      ( k4_subset_1(A_101,B_102,C_103) = k2_xboole_0(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_691,plain,(
    ! [A_109,B_110] :
      ( k4_subset_1(A_109,B_110,A_109) = k2_xboole_0(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_45,c_526])).

tff(c_714,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_691])).

tff(c_42,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_42])).

tff(c_724,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_46])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_375,plain,(
    ! [C_85,A_86,B_87] :
      ( r2_hidden(C_85,A_86)
      | ~ r2_hidden(C_85,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1002,plain,(
    ! [A_136,B_137,A_138] :
      ( r2_hidden('#skF_2'(A_136,B_137),A_138)
      | ~ m1_subset_1(A_136,k1_zfmisc_1(A_138))
      | r1_tarski(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_12,c_375])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1022,plain,(
    ! [A_139,A_140] :
      ( ~ m1_subset_1(A_139,k1_zfmisc_1(A_140))
      | r1_tarski(A_139,A_140) ) ),
    inference(resolution,[status(thm)],[c_1002,c_10])).

tff(c_1061,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1022])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1075,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1061,c_16])).

tff(c_101,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,k3_xboole_0(A_44,B_43)) = B_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_14])).

tff(c_1111,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_119])).

tff(c_18,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_175,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_212,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(B_59,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_22,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_218,plain,(
    ! [B_59,A_58] : k2_xboole_0(B_59,A_58) = k2_xboole_0(A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_22])).

tff(c_1122,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_218])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_1122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.53  
% 2.89/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.54  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.89/1.54  
% 2.89/1.54  %Foreground sorts:
% 2.89/1.54  
% 2.89/1.54  
% 2.89/1.54  %Background operators:
% 2.89/1.54  
% 2.89/1.54  
% 2.89/1.54  %Foreground operators:
% 2.89/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.54  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.89/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.89/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.54  
% 3.20/1.55  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.20/1.55  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.20/1.55  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.20/1.55  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.20/1.55  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.55  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.20/1.55  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.20/1.55  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.20/1.55  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.55  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.20/1.55  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.55  tff(c_32, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.55  tff(c_34, plain, (![A_25]: (m1_subset_1(k2_subset_1(A_25), k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.55  tff(c_45, plain, (![A_25]: (m1_subset_1(A_25, k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.20/1.55  tff(c_526, plain, (![A_101, B_102, C_103]: (k4_subset_1(A_101, B_102, C_103)=k2_xboole_0(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.55  tff(c_691, plain, (![A_109, B_110]: (k4_subset_1(A_109, B_110, A_109)=k2_xboole_0(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(resolution, [status(thm)], [c_45, c_526])).
% 3.20/1.55  tff(c_714, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_691])).
% 3.20/1.55  tff(c_42, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.55  tff(c_46, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_42])).
% 3.20/1.55  tff(c_724, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_714, c_46])).
% 3.20/1.55  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.55  tff(c_375, plain, (![C_85, A_86, B_87]: (r2_hidden(C_85, A_86) | ~r2_hidden(C_85, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.55  tff(c_1002, plain, (![A_136, B_137, A_138]: (r2_hidden('#skF_2'(A_136, B_137), A_138) | ~m1_subset_1(A_136, k1_zfmisc_1(A_138)) | r1_tarski(A_136, B_137))), inference(resolution, [status(thm)], [c_12, c_375])).
% 3.20/1.55  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.55  tff(c_1022, plain, (![A_139, A_140]: (~m1_subset_1(A_139, k1_zfmisc_1(A_140)) | r1_tarski(A_139, A_140))), inference(resolution, [status(thm)], [c_1002, c_10])).
% 3.20/1.55  tff(c_1061, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_1022])).
% 3.20/1.55  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.55  tff(c_1075, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1061, c_16])).
% 3.20/1.55  tff(c_101, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.55  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.55  tff(c_119, plain, (![B_43, A_44]: (k2_xboole_0(B_43, k3_xboole_0(A_44, B_43))=B_43)), inference(superposition, [status(thm), theory('equality')], [c_101, c_14])).
% 3.20/1.55  tff(c_1111, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1075, c_119])).
% 3.20/1.55  tff(c_18, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.20/1.55  tff(c_175, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.55  tff(c_212, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_18, c_175])).
% 3.20/1.55  tff(c_22, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.55  tff(c_218, plain, (![B_59, A_58]: (k2_xboole_0(B_59, A_58)=k2_xboole_0(A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_212, c_22])).
% 3.20/1.55  tff(c_1122, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1111, c_218])).
% 3.20/1.55  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_724, c_1122])).
% 3.20/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  Inference rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Ref     : 0
% 3.20/1.55  #Sup     : 263
% 3.20/1.55  #Fact    : 0
% 3.20/1.55  #Define  : 0
% 3.20/1.55  #Split   : 1
% 3.20/1.55  #Chain   : 0
% 3.20/1.55  #Close   : 0
% 3.20/1.55  
% 3.20/1.55  Ordering : KBO
% 3.20/1.55  
% 3.20/1.55  Simplification rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Subsume      : 68
% 3.20/1.55  #Demod        : 26
% 3.20/1.55  #Tautology    : 101
% 3.20/1.55  #SimpNegUnit  : 32
% 3.20/1.55  #BackRed      : 1
% 3.20/1.55  
% 3.20/1.55  #Partial instantiations: 0
% 3.20/1.55  #Strategies tried      : 1
% 3.20/1.55  
% 3.20/1.55  Timing (in seconds)
% 3.20/1.55  ----------------------
% 3.20/1.55  Preprocessing        : 0.32
% 3.20/1.55  Parsing              : 0.18
% 3.20/1.55  CNF conversion       : 0.02
% 3.20/1.55  Main loop            : 0.41
% 3.20/1.55  Inferencing          : 0.15
% 3.20/1.55  Reduction            : 0.13
% 3.20/1.55  Demodulation         : 0.09
% 3.20/1.55  BG Simplification    : 0.02
% 3.20/1.55  Subsumption          : 0.08
% 3.20/1.55  Abstraction          : 0.02
% 3.20/1.55  MUC search           : 0.00
% 3.20/1.55  Cooper               : 0.00
% 3.20/1.55  Total                : 0.76
% 3.20/1.55  Index Insertion      : 0.00
% 3.20/1.55  Index Deletion       : 0.00
% 3.20/1.55  Index Matching       : 0.00
% 3.20/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
