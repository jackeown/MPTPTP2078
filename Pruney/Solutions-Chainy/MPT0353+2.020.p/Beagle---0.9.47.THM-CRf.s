%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :   60 (  66 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 (  81 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_200,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_200])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | ~ m1_subset_1(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [B_46,A_9] :
      ( r1_tarski(B_46,A_9)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_95,c_12])).

tff(c_107,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_102])).

tff(c_123,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_8])).

tff(c_157,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_154])).

tff(c_277,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_408,plain,(
    ! [C_65] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_65)) = k4_xboole_0('#skF_4',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_277])).

tff(c_430,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_408])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_740,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,C_81) = k3_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3876,plain,(
    ! [A_142,B_143,B_144] :
      ( k9_subset_1(A_142,B_143,k3_subset_1(A_142,B_144)) = k3_xboole_0(B_143,k3_subset_1(A_142,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_34,c_740])).

tff(c_3896,plain,(
    ! [B_143] : k9_subset_1('#skF_3',B_143,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_143,k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_3876])).

tff(c_549,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_564,plain,(
    ! [C_71] : k7_subset_1('#skF_3','#skF_4',C_71) = k4_xboole_0('#skF_4',C_71) ),
    inference(resolution,[status(thm)],[c_46,c_549])).

tff(c_42,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_566,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_42])).

tff(c_4187,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3896,c_566])).

tff(c_4190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_4187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.09  
% 5.69/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.09  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.69/2.09  
% 5.69/2.09  %Foreground sorts:
% 5.69/2.09  
% 5.69/2.09  
% 5.69/2.09  %Background operators:
% 5.69/2.09  
% 5.69/2.09  
% 5.69/2.09  %Foreground operators:
% 5.69/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.69/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.69/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.69/2.09  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.69/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.69/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.69/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.69/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.69/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.69/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.69/2.09  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.69/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.09  
% 5.69/2.10  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 5.69/2.10  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.69/2.10  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.69/2.10  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.69/2.10  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.69/2.10  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.69/2.10  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.69/2.10  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.69/2.10  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.69/2.10  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.69/2.10  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.69/2.10  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.69/2.10  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.69/2.10  tff(c_200, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.69/2.10  tff(c_217, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_200])).
% 5.69/2.10  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.69/2.10  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.69/2.10  tff(c_36, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.69/2.10  tff(c_95, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | ~m1_subset_1(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.69/2.10  tff(c_12, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.69/2.10  tff(c_102, plain, (![B_46, A_9]: (r1_tarski(B_46, A_9) | ~m1_subset_1(B_46, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_95, c_12])).
% 5.69/2.10  tff(c_107, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_36, c_102])).
% 5.69/2.10  tff(c_123, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_107])).
% 5.69/2.10  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.69/2.10  tff(c_146, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_4])).
% 5.69/2.10  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.69/2.10  tff(c_154, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146, c_8])).
% 5.69/2.10  tff(c_157, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_154])).
% 5.69/2.10  tff(c_277, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.69/2.10  tff(c_408, plain, (![C_65]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_65))=k4_xboole_0('#skF_4', C_65))), inference(superposition, [status(thm), theory('equality')], [c_157, c_277])).
% 5.69/2.10  tff(c_430, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_217, c_408])).
% 5.69/2.10  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.69/2.10  tff(c_740, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, C_81)=k3_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.69/2.10  tff(c_3876, plain, (![A_142, B_143, B_144]: (k9_subset_1(A_142, B_143, k3_subset_1(A_142, B_144))=k3_xboole_0(B_143, k3_subset_1(A_142, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(A_142)))), inference(resolution, [status(thm)], [c_34, c_740])).
% 5.69/2.10  tff(c_3896, plain, (![B_143]: (k9_subset_1('#skF_3', B_143, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_143, k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_44, c_3876])).
% 5.69/2.10  tff(c_549, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.69/2.10  tff(c_564, plain, (![C_71]: (k7_subset_1('#skF_3', '#skF_4', C_71)=k4_xboole_0('#skF_4', C_71))), inference(resolution, [status(thm)], [c_46, c_549])).
% 5.69/2.10  tff(c_42, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.69/2.10  tff(c_566, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_42])).
% 5.69/2.10  tff(c_4187, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3896, c_566])).
% 5.69/2.10  tff(c_4190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_430, c_4187])).
% 5.69/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.10  
% 5.69/2.10  Inference rules
% 5.69/2.10  ----------------------
% 5.69/2.10  #Ref     : 0
% 5.69/2.10  #Sup     : 1081
% 5.69/2.10  #Fact    : 0
% 5.69/2.10  #Define  : 0
% 5.69/2.10  #Split   : 4
% 5.69/2.10  #Chain   : 0
% 5.69/2.10  #Close   : 0
% 5.69/2.10  
% 5.69/2.10  Ordering : KBO
% 5.69/2.10  
% 5.69/2.10  Simplification rules
% 5.69/2.10  ----------------------
% 5.69/2.10  #Subsume      : 24
% 5.69/2.10  #Demod        : 1180
% 5.69/2.10  #Tautology    : 583
% 5.69/2.10  #SimpNegUnit  : 3
% 5.69/2.10  #BackRed      : 14
% 5.69/2.10  
% 5.69/2.10  #Partial instantiations: 0
% 5.69/2.10  #Strategies tried      : 1
% 5.69/2.10  
% 5.69/2.10  Timing (in seconds)
% 5.69/2.10  ----------------------
% 5.69/2.10  Preprocessing        : 0.33
% 5.69/2.10  Parsing              : 0.17
% 5.69/2.10  CNF conversion       : 0.02
% 5.69/2.10  Main loop            : 1.01
% 5.69/2.10  Inferencing          : 0.32
% 5.69/2.10  Reduction            : 0.44
% 5.69/2.10  Demodulation         : 0.34
% 5.69/2.10  BG Simplification    : 0.04
% 5.69/2.10  Subsumption          : 0.15
% 5.69/2.10  Abstraction          : 0.05
% 5.69/2.10  MUC search           : 0.00
% 5.69/2.10  Cooper               : 0.00
% 5.69/2.10  Total                : 1.37
% 5.69/2.10  Index Insertion      : 0.00
% 5.69/2.10  Index Deletion       : 0.00
% 5.69/2.10  Index Matching       : 0.00
% 5.69/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
