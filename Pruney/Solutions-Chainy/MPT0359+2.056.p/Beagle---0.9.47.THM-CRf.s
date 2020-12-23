%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 131 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 204 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_34,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [C_43,A_44,B_45] :
      ( r2_hidden(C_43,A_44)
      | ~ r2_hidden(C_43,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [A_55,B_56,A_57] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_57)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(A_57))
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_58,A_59] :
      ( ~ m1_subset_1(A_58,k1_zfmisc_1(A_59))
      | r1_tarski(A_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_178,c_4])).

tff(c_203,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(resolution,[status(thm)],[c_34,c_190])).

tff(c_204,plain,(
    ! [A_60] : r1_tarski(k1_xboole_0,A_60) ),
    inference(resolution,[status(thm)],[c_34,c_190])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( k1_subset_1(A_23) = B_24
      | ~ r1_tarski(B_24,k3_subset_1(A_23,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_208,plain,(
    ! [A_23] :
      ( k1_subset_1(A_23) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_204,c_32])).

tff(c_213,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_208])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_216,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_47])).

tff(c_102,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [A_25] : k3_subset_1(A_25,k3_subset_1(A_25,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_241,plain,(
    ! [A_25] : k3_subset_1(A_25,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_108])).

tff(c_44,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | k2_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_73,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38,plain,
    ( k2_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_49,plain,
    ( '#skF_2' != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_81,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_49])).

tff(c_272,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_81])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_272])).

tff(c_278,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_277,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_308,plain,(
    ! [A_78,B_79] :
      ( k3_subset_1(A_78,k3_subset_1(A_78,B_79)) = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_320,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_308])).

tff(c_379,plain,(
    ! [A_88,B_89] :
      ( k1_subset_1(A_88) = B_89
      | ~ r1_tarski(B_89,k3_subset_1(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_382,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_379])).

tff(c_393,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_382])).

tff(c_395,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_398,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_395])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_398])).

tff(c_403,plain,(
    k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_405,plain,(
    k3_subset_1('#skF_2',k1_subset_1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_320])).

tff(c_431,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_47])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.24/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.31  
% 2.24/1.32  tff(f_76, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.24/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.24/1.32  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.24/1.32  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.24/1.32  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.24/1.32  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.24/1.32  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.24/1.32  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.24/1.32  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.24/1.32  tff(c_34, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.32  tff(c_109, plain, (![C_43, A_44, B_45]: (r2_hidden(C_43, A_44) | ~r2_hidden(C_43, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.32  tff(c_178, plain, (![A_55, B_56, A_57]: (r2_hidden('#skF_1'(A_55, B_56), A_57) | ~m1_subset_1(A_55, k1_zfmisc_1(A_57)) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_109])).
% 2.24/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.32  tff(c_190, plain, (![A_58, A_59]: (~m1_subset_1(A_58, k1_zfmisc_1(A_59)) | r1_tarski(A_58, A_59))), inference(resolution, [status(thm)], [c_178, c_4])).
% 2.24/1.32  tff(c_203, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(resolution, [status(thm)], [c_34, c_190])).
% 2.24/1.32  tff(c_204, plain, (![A_60]: (r1_tarski(k1_xboole_0, A_60))), inference(resolution, [status(thm)], [c_34, c_190])).
% 2.24/1.32  tff(c_32, plain, (![A_23, B_24]: (k1_subset_1(A_23)=B_24 | ~r1_tarski(B_24, k3_subset_1(A_23, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.24/1.32  tff(c_208, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_204, c_32])).
% 2.24/1.32  tff(c_213, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_208])).
% 2.24/1.32  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.32  tff(c_24, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.32  tff(c_47, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.24/1.32  tff(c_216, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_47])).
% 2.24/1.32  tff(c_102, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.32  tff(c_108, plain, (![A_25]: (k3_subset_1(A_25, k3_subset_1(A_25, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.24/1.32  tff(c_241, plain, (![A_25]: (k3_subset_1(A_25, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_216, c_108])).
% 2.24/1.32  tff(c_44, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | k2_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.24/1.32  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 2.24/1.32  tff(c_73, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 2.24/1.32  tff(c_38, plain, (k2_subset_1('#skF_2')!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.24/1.32  tff(c_49, plain, ('#skF_2'!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 2.24/1.32  tff(c_81, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_49])).
% 2.24/1.32  tff(c_272, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_81])).
% 2.24/1.32  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_272])).
% 2.24/1.32  tff(c_278, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.24/1.32  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.24/1.32  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.32  tff(c_277, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.24/1.32  tff(c_308, plain, (![A_78, B_79]: (k3_subset_1(A_78, k3_subset_1(A_78, B_79))=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.32  tff(c_320, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_308])).
% 2.24/1.32  tff(c_379, plain, (![A_88, B_89]: (k1_subset_1(A_88)=B_89 | ~r1_tarski(B_89, k3_subset_1(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.24/1.32  tff(c_382, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_379])).
% 2.24/1.32  tff(c_393, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_382])).
% 2.24/1.32  tff(c_395, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_393])).
% 2.24/1.32  tff(c_398, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_395])).
% 2.24/1.32  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_398])).
% 2.24/1.32  tff(c_403, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2')), inference(splitRight, [status(thm)], [c_393])).
% 2.24/1.32  tff(c_405, plain, (k3_subset_1('#skF_2', k1_subset_1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_320])).
% 2.24/1.32  tff(c_431, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_405, c_47])).
% 2.24/1.32  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_431])).
% 2.24/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  Inference rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Ref     : 0
% 2.24/1.32  #Sup     : 88
% 2.24/1.32  #Fact    : 0
% 2.24/1.32  #Define  : 0
% 2.24/1.32  #Split   : 3
% 2.24/1.32  #Chain   : 0
% 2.24/1.32  #Close   : 0
% 2.24/1.32  
% 2.24/1.32  Ordering : KBO
% 2.24/1.32  
% 2.24/1.32  Simplification rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Subsume      : 2
% 2.24/1.32  #Demod        : 46
% 2.24/1.32  #Tautology    : 53
% 2.24/1.32  #SimpNegUnit  : 1
% 2.24/1.32  #BackRed      : 9
% 2.24/1.32  
% 2.24/1.32  #Partial instantiations: 0
% 2.24/1.32  #Strategies tried      : 1
% 2.24/1.32  
% 2.24/1.32  Timing (in seconds)
% 2.24/1.32  ----------------------
% 2.24/1.33  Preprocessing        : 0.29
% 2.24/1.33  Parsing              : 0.16
% 2.24/1.33  CNF conversion       : 0.02
% 2.24/1.33  Main loop            : 0.26
% 2.24/1.33  Inferencing          : 0.08
% 2.24/1.33  Reduction            : 0.09
% 2.24/1.33  Demodulation         : 0.07
% 2.24/1.33  BG Simplification    : 0.02
% 2.24/1.33  Subsumption          : 0.06
% 2.24/1.33  Abstraction          : 0.01
% 2.24/1.33  MUC search           : 0.00
% 2.24/1.33  Cooper               : 0.00
% 2.24/1.33  Total                : 0.57
% 2.24/1.33  Index Insertion      : 0.00
% 2.24/1.33  Index Deletion       : 0.00
% 2.24/1.33  Index Matching       : 0.00
% 2.24/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
