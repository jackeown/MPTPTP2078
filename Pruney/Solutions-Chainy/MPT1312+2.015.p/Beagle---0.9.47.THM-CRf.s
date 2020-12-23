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
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 104 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_39,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_27,c_39])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [C_39,A_40,B_41] :
      ( m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ m1_pre_topc(B_41,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    ! [A_58,A_59,B_60] :
      ( m1_subset_1(A_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_pre_topc(B_60,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ r1_tarski(A_58,u1_struct_0(B_60)) ) ),
    inference(resolution,[status(thm)],[c_14,c_70])).

tff(c_137,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_58,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_135])).

tff(c_141,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_61,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_137])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_62,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_141,c_12])).

tff(c_166,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47,c_152])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_36,C_37,B_38] :
      ( m1_subset_1(A_36,C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_48,B_49,A_50] :
      ( m1_subset_1(A_48,B_49)
      | ~ r2_hidden(A_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_116,plain,(
    ! [A_55,B_56,B_57] :
      ( m1_subset_1(A_55,B_56)
      | ~ r1_tarski(B_57,B_56)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_55,B_57) ) ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_122,plain,(
    ! [A_55,B_2,A_1] :
      ( m1_subset_1(A_55,k1_zfmisc_1(B_2))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_55,k1_zfmisc_1(A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_186,plain,(
    ! [A_66,B_67,A_68] :
      ( m1_subset_1(A_66,k1_zfmisc_1(B_67))
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_68))
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_122])).

tff(c_213,plain,(
    ! [B_72] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(B_72))
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),B_72) ) ),
    inference(resolution,[status(thm)],[c_22,c_186])).

tff(c_235,plain,(
    ! [B_73] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(B_73)))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_73) ) ),
    inference(resolution,[status(thm)],[c_2,c_213])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_245,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_235,c_20])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.25  
% 2.30/1.25  %Foreground sorts:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Background operators:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Foreground operators:
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.25  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.30/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.30/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.25  
% 2.30/1.26  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.30/1.26  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.30/1.26  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.30/1.26  tff(f_73, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.30/1.26  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.30/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.30/1.26  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.30/1.26  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.30/1.26  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.30/1.26  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.26  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.26  tff(c_27, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.30/1.26  tff(c_39, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.26  tff(c_47, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(resolution, [status(thm)], [c_27, c_39])).
% 2.30/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.26  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.26  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.26  tff(c_70, plain, (![C_39, A_40, B_41]: (m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(B_41))) | ~m1_pre_topc(B_41, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.26  tff(c_135, plain, (![A_58, A_59, B_60]: (m1_subset_1(A_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_pre_topc(B_60, A_59) | ~l1_pre_topc(A_59) | ~r1_tarski(A_58, u1_struct_0(B_60)))), inference(resolution, [status(thm)], [c_14, c_70])).
% 2.30/1.26  tff(c_137, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_58, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_135])).
% 2.30/1.26  tff(c_141, plain, (![A_61]: (m1_subset_1(A_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_61, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_137])).
% 2.30/1.26  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.26  tff(c_152, plain, (![A_62]: (r1_tarski(A_62, u1_struct_0('#skF_1')) | ~r1_tarski(A_62, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_141, c_12])).
% 2.30/1.26  tff(c_166, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_47, c_152])).
% 2.30/1.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.26  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.26  tff(c_8, plain, (![A_5]: (~v1_xboole_0(k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.30/1.26  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.26  tff(c_60, plain, (![A_36, C_37, B_38]: (m1_subset_1(A_36, C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.26  tff(c_100, plain, (![A_48, B_49, A_50]: (m1_subset_1(A_48, B_49) | ~r2_hidden(A_48, A_50) | ~r1_tarski(A_50, B_49))), inference(resolution, [status(thm)], [c_14, c_60])).
% 2.30/1.26  tff(c_116, plain, (![A_55, B_56, B_57]: (m1_subset_1(A_55, B_56) | ~r1_tarski(B_57, B_56) | v1_xboole_0(B_57) | ~m1_subset_1(A_55, B_57))), inference(resolution, [status(thm)], [c_10, c_100])).
% 2.30/1.26  tff(c_122, plain, (![A_55, B_2, A_1]: (m1_subset_1(A_55, k1_zfmisc_1(B_2)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_55, k1_zfmisc_1(A_1)) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_116])).
% 2.30/1.26  tff(c_186, plain, (![A_66, B_67, A_68]: (m1_subset_1(A_66, k1_zfmisc_1(B_67)) | ~m1_subset_1(A_66, k1_zfmisc_1(A_68)) | ~r1_tarski(A_68, B_67))), inference(negUnitSimplification, [status(thm)], [c_8, c_122])).
% 2.30/1.26  tff(c_213, plain, (![B_72]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_72)) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), B_72))), inference(resolution, [status(thm)], [c_22, c_186])).
% 2.30/1.26  tff(c_235, plain, (![B_73]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(B_73))) | ~r1_tarski(u1_struct_0('#skF_2'), B_73))), inference(resolution, [status(thm)], [c_2, c_213])).
% 2.30/1.26  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.26  tff(c_245, plain, (~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_235, c_20])).
% 2.30/1.26  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_245])).
% 2.30/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.26  
% 2.30/1.26  Inference rules
% 2.30/1.26  ----------------------
% 2.30/1.26  #Ref     : 0
% 2.30/1.26  #Sup     : 53
% 2.30/1.26  #Fact    : 0
% 2.30/1.26  #Define  : 0
% 2.30/1.26  #Split   : 2
% 2.30/1.26  #Chain   : 0
% 2.30/1.26  #Close   : 0
% 2.30/1.26  
% 2.30/1.26  Ordering : KBO
% 2.30/1.26  
% 2.30/1.26  Simplification rules
% 2.30/1.26  ----------------------
% 2.30/1.26  #Subsume      : 1
% 2.43/1.26  #Demod        : 4
% 2.43/1.26  #Tautology    : 6
% 2.43/1.26  #SimpNegUnit  : 1
% 2.43/1.26  #BackRed      : 0
% 2.43/1.26  
% 2.43/1.26  #Partial instantiations: 0
% 2.43/1.26  #Strategies tried      : 1
% 2.43/1.26  
% 2.43/1.26  Timing (in seconds)
% 2.43/1.26  ----------------------
% 2.43/1.27  Preprocessing        : 0.27
% 2.43/1.27  Parsing              : 0.15
% 2.43/1.27  CNF conversion       : 0.02
% 2.43/1.27  Main loop            : 0.23
% 2.43/1.27  Inferencing          : 0.09
% 2.43/1.27  Reduction            : 0.06
% 2.43/1.27  Demodulation         : 0.04
% 2.43/1.27  BG Simplification    : 0.01
% 2.43/1.27  Subsumption          : 0.06
% 2.43/1.27  Abstraction          : 0.01
% 2.43/1.27  MUC search           : 0.00
% 2.43/1.27  Cooper               : 0.00
% 2.43/1.27  Total                : 0.53
% 2.43/1.27  Index Insertion      : 0.00
% 2.43/1.27  Index Deletion       : 0.00
% 2.43/1.27  Index Matching       : 0.00
% 2.43/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
