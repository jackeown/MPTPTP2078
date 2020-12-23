%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   56 (  66 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 116 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_18,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_39,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_78,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_39,c_78])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    ! [C_73,A_74,B_75] :
      ( m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(B_75)))
      | ~ m1_pre_topc(B_75,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_432,plain,(
    ! [A_98,A_99,B_100] :
      ( m1_subset_1(A_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ r1_tarski(A_98,u1_struct_0(B_100)) ) ),
    inference(resolution,[status(thm)],[c_26,c_217])).

tff(c_434,plain,(
    ! [A_98] :
      ( m1_subset_1(A_98,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_98,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_432])).

tff(c_442,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_101,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_434])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_462,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_101,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_442,c_24])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [C_64,B_65,A_66] :
      ( r2_hidden(C_64,B_65)
      | ~ r2_hidden(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_309,plain,(
    ! [B_90,B_91,A_92] :
      ( r2_hidden(B_90,B_91)
      | ~ r1_tarski(A_92,B_91)
      | ~ m1_subset_1(B_90,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_317,plain,(
    ! [B_90,B_7,A_6] :
      ( r2_hidden(B_90,k1_zfmisc_1(B_7))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_309])).

tff(c_511,plain,(
    ! [B_107,B_108,A_109] :
      ( r2_hidden(B_107,k1_zfmisc_1(B_108))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_109))
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_317])).

tff(c_561,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_4',k1_zfmisc_1(B_112))
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_3')),B_112) ) ),
    inference(resolution,[status(thm)],[c_34,c_511])).

tff(c_649,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_4',k1_zfmisc_1(k1_zfmisc_1(B_117)))
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_117) ) ),
    inference(resolution,[status(thm)],[c_8,c_561])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_659,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(B_117)))
      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(B_117)))
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_117) ) ),
    inference(resolution,[status(thm)],[c_649,c_10])).

tff(c_709,plain,(
    ! [B_122] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(B_122)))
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_659])).

tff(c_32,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_728,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_709,c_32])).

tff(c_731,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_462,c_728])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.64  
% 2.57/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.65  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.85/1.65  
% 2.85/1.65  %Foreground sorts:
% 2.85/1.65  
% 2.85/1.65  
% 2.85/1.65  %Background operators:
% 2.85/1.65  
% 2.85/1.65  
% 2.85/1.65  %Foreground operators:
% 2.85/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.65  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.85/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.65  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.85/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.65  
% 2.85/1.67  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.85/1.67  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.85/1.67  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.85/1.67  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.85/1.67  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.85/1.67  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.85/1.67  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.85/1.67  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.85/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.85/1.67  tff(c_18, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.85/1.67  tff(c_20, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.85/1.67  tff(c_39, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.85/1.67  tff(c_78, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.67  tff(c_95, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(resolution, [status(thm)], [c_39, c_78])).
% 2.85/1.67  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.67  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.67  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.67  tff(c_217, plain, (![C_73, A_74, B_75]: (m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(B_75))) | ~m1_pre_topc(B_75, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.67  tff(c_432, plain, (![A_98, A_99, B_100]: (m1_subset_1(A_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99) | ~r1_tarski(A_98, u1_struct_0(B_100)))), inference(resolution, [status(thm)], [c_26, c_217])).
% 2.85/1.67  tff(c_434, plain, (![A_98]: (m1_subset_1(A_98, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_98, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_432])).
% 2.85/1.67  tff(c_442, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_101, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_434])).
% 2.85/1.67  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.67  tff(c_462, plain, (![A_101]: (r1_tarski(A_101, u1_struct_0('#skF_2')) | ~r1_tarski(A_101, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_442, c_24])).
% 2.85/1.67  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.85/1.67  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.85/1.67  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.67  tff(c_12, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.85/1.67  tff(c_169, plain, (![C_64, B_65, A_66]: (r2_hidden(C_64, B_65) | ~r2_hidden(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.67  tff(c_309, plain, (![B_90, B_91, A_92]: (r2_hidden(B_90, B_91) | ~r1_tarski(A_92, B_91) | ~m1_subset_1(B_90, A_92) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_12, c_169])).
% 2.85/1.67  tff(c_317, plain, (![B_90, B_7, A_6]: (r2_hidden(B_90, k1_zfmisc_1(B_7)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_309])).
% 2.85/1.67  tff(c_511, plain, (![B_107, B_108, A_109]: (r2_hidden(B_107, k1_zfmisc_1(B_108)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_109)) | ~r1_tarski(A_109, B_108))), inference(negUnitSimplification, [status(thm)], [c_22, c_317])).
% 2.85/1.67  tff(c_561, plain, (![B_112]: (r2_hidden('#skF_4', k1_zfmisc_1(B_112)) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_3')), B_112))), inference(resolution, [status(thm)], [c_34, c_511])).
% 2.85/1.67  tff(c_649, plain, (![B_117]: (r2_hidden('#skF_4', k1_zfmisc_1(k1_zfmisc_1(B_117))) | ~r1_tarski(u1_struct_0('#skF_3'), B_117))), inference(resolution, [status(thm)], [c_8, c_561])).
% 2.85/1.67  tff(c_10, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.85/1.67  tff(c_659, plain, (![B_117]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(B_117))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(B_117))) | ~r1_tarski(u1_struct_0('#skF_3'), B_117))), inference(resolution, [status(thm)], [c_649, c_10])).
% 2.85/1.67  tff(c_709, plain, (![B_122]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(B_122))) | ~r1_tarski(u1_struct_0('#skF_3'), B_122))), inference(negUnitSimplification, [status(thm)], [c_22, c_659])).
% 2.85/1.67  tff(c_32, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.67  tff(c_728, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_709, c_32])).
% 2.85/1.67  tff(c_731, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_462, c_728])).
% 2.85/1.67  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_731])).
% 2.85/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.67  
% 2.85/1.67  Inference rules
% 2.85/1.67  ----------------------
% 2.85/1.67  #Ref     : 0
% 2.85/1.67  #Sup     : 158
% 2.85/1.67  #Fact    : 0
% 2.85/1.67  #Define  : 0
% 2.85/1.67  #Split   : 4
% 2.85/1.67  #Chain   : 0
% 2.85/1.67  #Close   : 0
% 2.85/1.67  
% 2.85/1.67  Ordering : KBO
% 2.85/1.67  
% 2.85/1.67  Simplification rules
% 2.85/1.67  ----------------------
% 2.85/1.67  #Subsume      : 59
% 2.85/1.67  #Demod        : 10
% 2.85/1.67  #Tautology    : 17
% 2.85/1.67  #SimpNegUnit  : 17
% 2.85/1.67  #BackRed      : 1
% 2.85/1.67  
% 2.85/1.67  #Partial instantiations: 0
% 2.85/1.67  #Strategies tried      : 1
% 2.85/1.67  
% 2.85/1.67  Timing (in seconds)
% 2.85/1.67  ----------------------
% 2.85/1.67  Preprocessing        : 0.38
% 2.85/1.67  Parsing              : 0.20
% 2.85/1.67  CNF conversion       : 0.03
% 2.85/1.67  Main loop            : 0.37
% 2.85/1.67  Inferencing          : 0.14
% 2.85/1.67  Reduction            : 0.10
% 2.85/1.67  Demodulation         : 0.06
% 2.85/1.67  BG Simplification    : 0.02
% 2.85/1.67  Subsumption          : 0.09
% 2.85/1.67  Abstraction          : 0.01
% 2.85/1.67  MUC search           : 0.00
% 2.85/1.67  Cooper               : 0.00
% 2.85/1.67  Total                : 0.79
% 2.85/1.67  Index Insertion      : 0.00
% 2.85/1.67  Index Deletion       : 0.00
% 2.85/1.67  Index Matching       : 0.00
% 2.85/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
