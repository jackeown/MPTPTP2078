%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   64 (  71 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 (  76 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_77,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    ! [A_42] : k2_subset_1(A_42) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_49,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [B_41,A_40] :
      ( r2_hidden(B_41,A_40)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_39] : k3_tarski(k1_zfmisc_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_126,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_146,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k3_tarski(A_71),k3_tarski(B_72))
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,k3_tarski(B_87))
      | ~ r1_tarski(k1_tarski(A_86),B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_146])).

tff(c_245,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,k3_tarski(B_93))
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_22,c_231])).

tff(c_280,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(A_96,A_97)
      | ~ r2_hidden(A_96,k1_zfmisc_1(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_245])).

tff(c_284,plain,(
    ! [B_41,A_97] :
      ( r1_tarski(B_41,A_97)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_97))
      | v1_xboole_0(k1_zfmisc_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_32,c_280])).

tff(c_297,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_284])).

tff(c_310,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_297])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_310,c_4])).

tff(c_40,plain,(
    ! [A_43] : m1_subset_1(k2_subset_1(A_43),k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_43] : m1_subset_1(A_43,k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_379,plain,(
    ! [A_118,B_119,C_120] :
      ( k4_subset_1(A_118,B_119,C_120) = k2_xboole_0(B_119,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1054,plain,(
    ! [A_199,B_200] :
      ( k4_subset_1(A_199,B_200,A_199) = k2_xboole_0(B_200,A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(resolution,[status(thm)],[c_50,c_379])).

tff(c_1061,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1054])).

tff(c_1066,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_1061])).

tff(c_1068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_1066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.46  
% 3.16/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 3.16/1.46  
% 3.16/1.46  %Foreground sorts:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Background operators:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Foreground operators:
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.46  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.16/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.16/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.46  
% 3.31/1.47  tff(f_72, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.31/1.47  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.31/1.47  tff(f_77, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.31/1.47  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.31/1.47  tff(f_57, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.31/1.47  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.31/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.31/1.47  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.31/1.47  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.31/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.31/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.31/1.47  tff(f_74, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.31/1.47  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.31/1.47  tff(c_38, plain, (![A_42]: (k2_subset_1(A_42)=A_42)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.47  tff(c_46, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.47  tff(c_49, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_46])).
% 3.31/1.47  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.47  tff(c_42, plain, (![A_44]: (~v1_xboole_0(k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.47  tff(c_32, plain, (![B_41, A_40]: (r2_hidden(B_41, A_40) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.31/1.47  tff(c_28, plain, (![A_39]: (k3_tarski(k1_zfmisc_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.47  tff(c_22, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.31/1.47  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.47  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.47  tff(c_114, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.31/1.47  tff(c_123, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_114])).
% 3.31/1.47  tff(c_126, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_123])).
% 3.31/1.47  tff(c_146, plain, (![A_71, B_72]: (r1_tarski(k3_tarski(A_71), k3_tarski(B_72)) | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.31/1.47  tff(c_231, plain, (![A_86, B_87]: (r1_tarski(A_86, k3_tarski(B_87)) | ~r1_tarski(k1_tarski(A_86), B_87))), inference(superposition, [status(thm), theory('equality')], [c_126, c_146])).
% 3.31/1.47  tff(c_245, plain, (![A_92, B_93]: (r1_tarski(A_92, k3_tarski(B_93)) | ~r2_hidden(A_92, B_93))), inference(resolution, [status(thm)], [c_22, c_231])).
% 3.31/1.47  tff(c_280, plain, (![A_96, A_97]: (r1_tarski(A_96, A_97) | ~r2_hidden(A_96, k1_zfmisc_1(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_245])).
% 3.31/1.47  tff(c_284, plain, (![B_41, A_97]: (r1_tarski(B_41, A_97) | ~m1_subset_1(B_41, k1_zfmisc_1(A_97)) | v1_xboole_0(k1_zfmisc_1(A_97)))), inference(resolution, [status(thm)], [c_32, c_280])).
% 3.31/1.47  tff(c_297, plain, (![B_103, A_104]: (r1_tarski(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)))), inference(negUnitSimplification, [status(thm)], [c_42, c_284])).
% 3.31/1.47  tff(c_310, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_297])).
% 3.31/1.47  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.47  tff(c_337, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_310, c_4])).
% 3.31/1.47  tff(c_40, plain, (![A_43]: (m1_subset_1(k2_subset_1(A_43), k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.31/1.47  tff(c_50, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.31/1.47  tff(c_379, plain, (![A_118, B_119, C_120]: (k4_subset_1(A_118, B_119, C_120)=k2_xboole_0(B_119, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.31/1.47  tff(c_1054, plain, (![A_199, B_200]: (k4_subset_1(A_199, B_200, A_199)=k2_xboole_0(B_200, A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(resolution, [status(thm)], [c_50, c_379])).
% 3.31/1.47  tff(c_1061, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1054])).
% 3.31/1.47  tff(c_1066, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_337, c_1061])).
% 3.31/1.47  tff(c_1068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_1066])).
% 3.31/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  
% 3.31/1.47  Inference rules
% 3.31/1.47  ----------------------
% 3.31/1.47  #Ref     : 0
% 3.31/1.47  #Sup     : 219
% 3.31/1.47  #Fact    : 0
% 3.31/1.47  #Define  : 0
% 3.31/1.47  #Split   : 0
% 3.31/1.47  #Chain   : 0
% 3.31/1.47  #Close   : 0
% 3.31/1.47  
% 3.31/1.47  Ordering : KBO
% 3.31/1.47  
% 3.31/1.47  Simplification rules
% 3.31/1.47  ----------------------
% 3.31/1.47  #Subsume      : 21
% 3.31/1.47  #Demod        : 72
% 3.31/1.47  #Tautology    : 77
% 3.31/1.47  #SimpNegUnit  : 7
% 3.31/1.47  #BackRed      : 0
% 3.31/1.47  
% 3.31/1.47  #Partial instantiations: 0
% 3.31/1.47  #Strategies tried      : 1
% 3.31/1.47  
% 3.31/1.47  Timing (in seconds)
% 3.31/1.47  ----------------------
% 3.31/1.48  Preprocessing        : 0.32
% 3.31/1.48  Parsing              : 0.18
% 3.31/1.48  CNF conversion       : 0.02
% 3.31/1.48  Main loop            : 0.39
% 3.31/1.48  Inferencing          : 0.16
% 3.31/1.48  Reduction            : 0.11
% 3.31/1.48  Demodulation         : 0.08
% 3.31/1.48  BG Simplification    : 0.02
% 3.31/1.48  Subsumption          : 0.08
% 3.31/1.48  Abstraction          : 0.02
% 3.31/1.48  MUC search           : 0.00
% 3.31/1.48  Cooper               : 0.00
% 3.31/1.48  Total                : 0.74
% 3.31/1.48  Index Insertion      : 0.00
% 3.31/1.48  Index Deletion       : 0.00
% 3.31/1.48  Index Matching       : 0.00
% 3.31/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
