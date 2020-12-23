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
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 152 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_268,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k3_subset_1(A_78,B_79),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_234,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,A_72)
      | ~ m1_subset_1(B_71,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_241,plain,(
    ! [B_71,A_9] :
      ( r1_tarski(B_71,A_9)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_234,c_8])).

tff(c_245,plain,(
    ! [B_71,A_9] :
      ( r1_tarski(B_71,A_9)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_241])).

tff(c_275,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k3_subset_1(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_268,c_245])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_71,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_194,plain,(
    ! [A_63] :
      ( r1_xboole_0(A_63,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_63,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_197,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_194,c_71])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_197])).

tff(c_204,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_204])).

tff(c_207,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_208,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_278,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_298,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_278])).

tff(c_336,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(A_88,k4_xboole_0(B_89,C_90))
      | ~ r1_xboole_0(A_88,C_90)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_342,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_88,'#skF_4')
      | ~ r1_tarski(A_88,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_336])).

tff(c_438,plain,(
    ! [B_105,C_106,A_107] :
      ( r1_tarski(B_105,C_106)
      | ~ r1_tarski(k3_subset_1(A_107,C_106),k3_subset_1(A_107,B_105))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_446,plain,(
    ! [C_106] :
      ( r1_tarski('#skF_4',C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ r1_xboole_0(k3_subset_1('#skF_3',C_106),'#skF_4')
      | ~ r1_tarski(k3_subset_1('#skF_3',C_106),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_342,c_438])).

tff(c_1031,plain,(
    ! [C_171] :
      ( r1_tarski('#skF_4',C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1('#skF_3'))
      | ~ r1_xboole_0(k3_subset_1('#skF_3',C_171),'#skF_4')
      | ~ r1_tarski(k3_subset_1('#skF_3',C_171),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_446])).

tff(c_1054,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_1031])).

tff(c_1067,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1054])).

tff(c_1068,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_1067])).

tff(c_1071,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_275,c_1068])).

tff(c_1075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.20/1.47  
% 3.20/1.47  %Foreground sorts:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Background operators:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Foreground operators:
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.20/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.47  
% 3.20/1.49  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 3.20/1.49  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.20/1.49  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.20/1.49  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.20/1.49  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.20/1.49  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.20/1.49  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.20/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.20/1.49  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.20/1.49  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.20/1.49  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.49  tff(c_268, plain, (![A_78, B_79]: (m1_subset_1(k3_subset_1(A_78, B_79), k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.49  tff(c_32, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.49  tff(c_234, plain, (![B_71, A_72]: (r2_hidden(B_71, A_72) | ~m1_subset_1(B_71, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.49  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.49  tff(c_241, plain, (![B_71, A_9]: (r1_tarski(B_71, A_9) | ~m1_subset_1(B_71, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_234, c_8])).
% 3.20/1.49  tff(c_245, plain, (![B_71, A_9]: (r1_tarski(B_71, A_9) | ~m1_subset_1(B_71, k1_zfmisc_1(A_9)))), inference(negUnitSimplification, [status(thm)], [c_32, c_241])).
% 3.20/1.49  tff(c_275, plain, (![A_78, B_79]: (r1_tarski(k3_subset_1(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_268, c_245])).
% 3.20/1.49  tff(c_42, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.49  tff(c_71, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.20/1.49  tff(c_48, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.49  tff(c_72, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.20/1.49  tff(c_133, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.49  tff(c_154, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_133])).
% 3.20/1.49  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.49  tff(c_194, plain, (![A_63]: (r1_xboole_0(A_63, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_63, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 3.20/1.49  tff(c_197, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_194, c_71])).
% 3.20/1.49  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_197])).
% 3.20/1.49  tff(c_204, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 3.20/1.49  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_204])).
% 3.20/1.49  tff(c_207, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 3.20/1.49  tff(c_208, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_42])).
% 3.20/1.49  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.49  tff(c_211, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_208, c_2])).
% 3.20/1.49  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.49  tff(c_278, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.49  tff(c_298, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_278])).
% 3.20/1.49  tff(c_336, plain, (![A_88, B_89, C_90]: (r1_tarski(A_88, k4_xboole_0(B_89, C_90)) | ~r1_xboole_0(A_88, C_90) | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.49  tff(c_342, plain, (![A_88]: (r1_tarski(A_88, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_88, '#skF_4') | ~r1_tarski(A_88, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_336])).
% 3.20/1.49  tff(c_438, plain, (![B_105, C_106, A_107]: (r1_tarski(B_105, C_106) | ~r1_tarski(k3_subset_1(A_107, C_106), k3_subset_1(A_107, B_105)) | ~m1_subset_1(C_106, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.49  tff(c_446, plain, (![C_106]: (r1_tarski('#skF_4', C_106) | ~m1_subset_1(C_106, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_xboole_0(k3_subset_1('#skF_3', C_106), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', C_106), '#skF_3'))), inference(resolution, [status(thm)], [c_342, c_438])).
% 3.20/1.49  tff(c_1031, plain, (![C_171]: (r1_tarski('#skF_4', C_171) | ~m1_subset_1(C_171, k1_zfmisc_1('#skF_3')) | ~r1_xboole_0(k3_subset_1('#skF_3', C_171), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', C_171), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_446])).
% 3.20/1.49  tff(c_1054, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_211, c_1031])).
% 3.20/1.49  tff(c_1067, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1054])).
% 3.20/1.49  tff(c_1068, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_207, c_1067])).
% 3.20/1.49  tff(c_1071, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_275, c_1068])).
% 3.20/1.49  tff(c_1075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1071])).
% 3.20/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  Inference rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Ref     : 0
% 3.20/1.49  #Sup     : 240
% 3.20/1.49  #Fact    : 0
% 3.20/1.49  #Define  : 0
% 3.20/1.49  #Split   : 2
% 3.20/1.49  #Chain   : 0
% 3.20/1.49  #Close   : 0
% 3.20/1.49  
% 3.20/1.49  Ordering : KBO
% 3.20/1.49  
% 3.20/1.49  Simplification rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Subsume      : 44
% 3.20/1.49  #Demod        : 51
% 3.20/1.49  #Tautology    : 54
% 3.20/1.49  #SimpNegUnit  : 18
% 3.20/1.49  #BackRed      : 0
% 3.20/1.49  
% 3.20/1.49  #Partial instantiations: 0
% 3.20/1.49  #Strategies tried      : 1
% 3.20/1.49  
% 3.20/1.49  Timing (in seconds)
% 3.20/1.49  ----------------------
% 3.20/1.49  Preprocessing        : 0.30
% 3.20/1.49  Parsing              : 0.15
% 3.20/1.49  CNF conversion       : 0.02
% 3.20/1.49  Main loop            : 0.45
% 3.20/1.49  Inferencing          : 0.18
% 3.20/1.49  Reduction            : 0.12
% 3.20/1.49  Demodulation         : 0.07
% 3.20/1.49  BG Simplification    : 0.03
% 3.20/1.49  Subsumption          : 0.09
% 3.20/1.49  Abstraction          : 0.03
% 3.20/1.49  MUC search           : 0.00
% 3.20/1.49  Cooper               : 0.00
% 3.20/1.49  Total                : 0.78
% 3.20/1.49  Index Insertion      : 0.00
% 3.20/1.49  Index Deletion       : 0.00
% 3.20/1.49  Index Matching       : 0.00
% 3.20/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
