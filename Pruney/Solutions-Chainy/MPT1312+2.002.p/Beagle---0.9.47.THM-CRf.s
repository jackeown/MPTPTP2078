%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  93 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_99,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_99,c_20])).

tff(c_10,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_72,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_27,c_72])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_244,plain,(
    ! [C_50,A_51,B_52] :
      ( m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(B_52)))
      | ~ m1_pre_topc(B_52,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_398,plain,(
    ! [A_66,A_67,B_68] :
      ( m1_subset_1(A_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_68,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ r1_tarski(A_66,u1_struct_0(B_68)) ) ),
    inference(resolution,[status(thm)],[c_16,c_244])).

tff(c_400,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_66,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_398])).

tff(c_404,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_69,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_400])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_412,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_70,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_404,c_14])).

tff(c_422,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_412])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_108,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_zfmisc_1(A_37),k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(k1_zfmisc_1(A_46),k1_zfmisc_1(B_47)) = k1_zfmisc_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_108,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,k2_xboole_0(C_40,B_41))
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_39,B_2,A_1] :
      ( r1_tarski(A_39,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_39,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_357,plain,(
    ! [A_62,B_63,A_64] :
      ( r1_tarski(A_62,k1_zfmisc_1(B_63))
      | ~ r1_tarski(A_62,k1_zfmisc_1(A_64))
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_122])).

tff(c_370,plain,(
    ! [B_63] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(B_63))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_63) ) ),
    inference(resolution,[status(thm)],[c_79,c_357])).

tff(c_425,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_422,c_370])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:53:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  %$ r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.29  
% 2.22/1.29  %Foreground sorts:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Background operators:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Foreground operators:
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.22/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.22/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.29  
% 2.51/1.31  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.31  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.51/1.31  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.51/1.31  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.51/1.31  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.51/1.31  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.51/1.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.51/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.51/1.31  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.51/1.31  tff(c_99, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.31  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.31  tff(c_107, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_99, c_20])).
% 2.51/1.31  tff(c_10, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.31  tff(c_12, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.31  tff(c_27, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.51/1.31  tff(c_72, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.31  tff(c_80, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(resolution, [status(thm)], [c_27, c_72])).
% 2.51/1.31  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.31  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.31  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.31  tff(c_244, plain, (![C_50, A_51, B_52]: (m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(B_52))) | ~m1_pre_topc(B_52, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.51/1.31  tff(c_398, plain, (![A_66, A_67, B_68]: (m1_subset_1(A_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_68, A_67) | ~l1_pre_topc(A_67) | ~r1_tarski(A_66, u1_struct_0(B_68)))), inference(resolution, [status(thm)], [c_16, c_244])).
% 2.51/1.31  tff(c_400, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_66, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_398])).
% 2.51/1.31  tff(c_404, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_69, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_400])).
% 2.51/1.31  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.31  tff(c_412, plain, (![A_70]: (r1_tarski(A_70, u1_struct_0('#skF_1')) | ~r1_tarski(A_70, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_404, c_14])).
% 2.51/1.31  tff(c_422, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_412])).
% 2.51/1.31  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.31  tff(c_79, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.51/1.31  tff(c_108, plain, (![A_37, B_38]: (r1_tarski(k1_zfmisc_1(A_37), k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.31  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.31  tff(c_156, plain, (![A_46, B_47]: (k2_xboole_0(k1_zfmisc_1(A_46), k1_zfmisc_1(B_47))=k1_zfmisc_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_108, c_6])).
% 2.51/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.31  tff(c_113, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, k2_xboole_0(C_40, B_41)) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.31  tff(c_122, plain, (![A_39, B_2, A_1]: (r1_tarski(A_39, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_39, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 2.51/1.31  tff(c_357, plain, (![A_62, B_63, A_64]: (r1_tarski(A_62, k1_zfmisc_1(B_63)) | ~r1_tarski(A_62, k1_zfmisc_1(A_64)) | ~r1_tarski(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_156, c_122])).
% 2.51/1.31  tff(c_370, plain, (![B_63]: (r1_tarski('#skF_3', k1_zfmisc_1(B_63)) | ~r1_tarski(u1_struct_0('#skF_2'), B_63))), inference(resolution, [status(thm)], [c_79, c_357])).
% 2.51/1.31  tff(c_425, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_422, c_370])).
% 2.51/1.31  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_425])).
% 2.51/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.31  
% 2.51/1.31  Inference rules
% 2.51/1.31  ----------------------
% 2.51/1.31  #Ref     : 0
% 2.51/1.31  #Sup     : 101
% 2.51/1.31  #Fact    : 0
% 2.51/1.31  #Define  : 0
% 2.51/1.31  #Split   : 1
% 2.51/1.31  #Chain   : 0
% 2.51/1.31  #Close   : 0
% 2.51/1.31  
% 2.51/1.31  Ordering : KBO
% 2.51/1.31  
% 2.51/1.31  Simplification rules
% 2.51/1.31  ----------------------
% 2.51/1.31  #Subsume      : 14
% 2.51/1.31  #Demod        : 10
% 2.51/1.31  #Tautology    : 35
% 2.51/1.31  #SimpNegUnit  : 1
% 2.51/1.31  #BackRed      : 0
% 2.51/1.31  
% 2.51/1.31  #Partial instantiations: 0
% 2.51/1.31  #Strategies tried      : 1
% 2.51/1.31  
% 2.51/1.31  Timing (in seconds)
% 2.51/1.31  ----------------------
% 2.51/1.31  Preprocessing        : 0.28
% 2.51/1.31  Parsing              : 0.16
% 2.51/1.31  CNF conversion       : 0.02
% 2.51/1.31  Main loop            : 0.26
% 2.51/1.31  Inferencing          : 0.10
% 2.51/1.31  Reduction            : 0.08
% 2.51/1.31  Demodulation         : 0.06
% 2.51/1.31  BG Simplification    : 0.01
% 2.51/1.31  Subsumption          : 0.06
% 2.51/1.31  Abstraction          : 0.01
% 2.51/1.31  MUC search           : 0.00
% 2.51/1.31  Cooper               : 0.00
% 2.51/1.31  Total                : 0.57
% 2.51/1.31  Index Insertion      : 0.00
% 2.51/1.31  Index Deletion       : 0.00
% 2.51/1.31  Index Matching       : 0.00
% 2.51/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
