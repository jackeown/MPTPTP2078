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
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 122 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_16,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_496,plain,(
    ! [A_84,B_85,B_86] :
      ( k9_subset_1(A_84,B_85,k3_subset_1(A_84,B_86)) = k3_xboole_0(B_85,k3_subset_1(A_84,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_543,plain,(
    ! [B_85] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_85,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k3_xboole_0(B_85,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_496])).

tff(c_249,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,k3_subset_1(A_60,C_62)) = k7_subset_1(A_60,B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_281,plain,(
    ! [B_61] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_61,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_20,c_249])).

tff(c_1523,plain,(
    ! [B_149] :
      ( k3_xboole_0(B_149,k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_149,'#skF_3')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_281])).

tff(c_1629,plain,(
    k3_xboole_0('#skF_2',k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3')) = k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1523])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_156,plain,(
    ! [B_49] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_49,'#skF_2') = k3_xboole_0(B_49,'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [B_49] :
      ( m1_subset_1(k3_xboole_0(B_49,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_8])).

tff(c_170,plain,(
    ! [B_50] : m1_subset_1(k3_xboole_0(B_50,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_162])).

tff(c_176,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_2',B_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_170])).

tff(c_407,plain,(
    ! [B_76,A_77,C_78] :
      ( v1_tops_2(B_76,A_77)
      | ~ v1_tops_2(C_78,A_77)
      | ~ r1_tarski(B_76,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_77))))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_77))))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_981,plain,(
    ! [A_118,B_119,A_120] :
      ( v1_tops_2(k3_xboole_0(A_118,B_119),A_120)
      | ~ v1_tops_2(A_118,A_120)
      | ~ m1_subset_1(A_118,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120))))
      | ~ m1_subset_1(k3_xboole_0(A_118,B_119),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120))))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_2,c_407])).

tff(c_1026,plain,(
    ! [B_2] :
      ( v1_tops_2(k3_xboole_0('#skF_2',B_2),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_176,c_981])).

tff(c_1086,plain,(
    ! [B_2] : v1_tops_2(k3_xboole_0('#skF_2',B_2),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_1026])).

tff(c_1710,plain,(
    v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1629,c_1086])).

tff(c_1750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:17:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.65  
% 3.86/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.65  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.86/1.65  
% 3.86/1.65  %Foreground sorts:
% 3.86/1.65  
% 3.86/1.65  
% 3.86/1.65  %Background operators:
% 3.86/1.65  
% 3.86/1.65  
% 3.86/1.65  %Foreground operators:
% 3.86/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.65  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.86/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.86/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.65  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.86/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.86/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.65  
% 3.86/1.66  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 3.86/1.66  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.86/1.66  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.86/1.66  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 3.86/1.66  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.86/1.66  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.86/1.66  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.86/1.66  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 3.86/1.66  tff(c_16, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.66  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.66  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.66  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.86/1.66  tff(c_116, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.86/1.66  tff(c_496, plain, (![A_84, B_85, B_86]: (k9_subset_1(A_84, B_85, k3_subset_1(A_84, B_86))=k3_xboole_0(B_85, k3_subset_1(A_84, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_6, c_116])).
% 3.86/1.66  tff(c_543, plain, (![B_85]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_85, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k3_xboole_0(B_85, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3')))), inference(resolution, [status(thm)], [c_20, c_496])).
% 3.86/1.66  tff(c_249, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, k3_subset_1(A_60, C_62))=k7_subset_1(A_60, B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.66  tff(c_281, plain, (![B_61]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_61, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_20, c_249])).
% 3.86/1.66  tff(c_1523, plain, (![B_149]: (k3_xboole_0(B_149, k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_149, '#skF_3') | ~m1_subset_1(B_149, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_281])).
% 3.86/1.66  tff(c_1629, plain, (k3_xboole_0('#skF_2', k3_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3'))=k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_1523])).
% 3.86/1.66  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.66  tff(c_18, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.66  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.66  tff(c_26, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.66  tff(c_30, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_26])).
% 3.86/1.66  tff(c_156, plain, (![B_49]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_49, '#skF_2')=k3_xboole_0(B_49, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_116])).
% 3.86/1.66  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.86/1.66  tff(c_162, plain, (![B_49]: (m1_subset_1(k3_xboole_0(B_49, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_156, c_8])).
% 3.86/1.66  tff(c_170, plain, (![B_50]: (m1_subset_1(k3_xboole_0(B_50, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_162])).
% 3.86/1.66  tff(c_176, plain, (![B_2]: (m1_subset_1(k3_xboole_0('#skF_2', B_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_170])).
% 3.86/1.66  tff(c_407, plain, (![B_76, A_77, C_78]: (v1_tops_2(B_76, A_77) | ~v1_tops_2(C_78, A_77) | ~r1_tarski(B_76, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_77)))) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_77)))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.86/1.66  tff(c_981, plain, (![A_118, B_119, A_120]: (v1_tops_2(k3_xboole_0(A_118, B_119), A_120) | ~v1_tops_2(A_118, A_120) | ~m1_subset_1(A_118, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120)))) | ~m1_subset_1(k3_xboole_0(A_118, B_119), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120)))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_2, c_407])).
% 3.86/1.66  tff(c_1026, plain, (![B_2]: (v1_tops_2(k3_xboole_0('#skF_2', B_2), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_176, c_981])).
% 3.86/1.66  tff(c_1086, plain, (![B_2]: (v1_tops_2(k3_xboole_0('#skF_2', B_2), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_1026])).
% 3.86/1.66  tff(c_1710, plain, (v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1629, c_1086])).
% 3.86/1.66  tff(c_1750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_1710])).
% 3.86/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.66  
% 3.86/1.66  Inference rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Ref     : 0
% 3.86/1.66  #Sup     : 433
% 3.86/1.66  #Fact    : 0
% 3.86/1.66  #Define  : 0
% 3.86/1.66  #Split   : 1
% 3.86/1.66  #Chain   : 0
% 3.86/1.66  #Close   : 0
% 3.86/1.66  
% 3.86/1.66  Ordering : KBO
% 3.86/1.66  
% 3.86/1.66  Simplification rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Subsume      : 1
% 3.86/1.66  #Demod        : 191
% 3.86/1.66  #Tautology    : 135
% 3.86/1.66  #SimpNegUnit  : 1
% 3.86/1.66  #BackRed      : 2
% 3.86/1.66  
% 3.86/1.66  #Partial instantiations: 0
% 3.86/1.66  #Strategies tried      : 1
% 3.86/1.66  
% 3.86/1.66  Timing (in seconds)
% 3.86/1.66  ----------------------
% 3.86/1.67  Preprocessing        : 0.31
% 3.86/1.67  Parsing              : 0.17
% 3.86/1.67  CNF conversion       : 0.02
% 3.86/1.67  Main loop            : 0.57
% 3.86/1.67  Inferencing          : 0.19
% 3.86/1.67  Reduction            : 0.21
% 3.86/1.67  Demodulation         : 0.16
% 3.86/1.67  BG Simplification    : 0.03
% 3.86/1.67  Subsumption          : 0.09
% 3.86/1.67  Abstraction          : 0.04
% 3.86/1.67  MUC search           : 0.00
% 3.86/1.67  Cooper               : 0.00
% 3.86/1.67  Total                : 0.91
% 3.86/1.67  Index Insertion      : 0.00
% 3.86/1.67  Index Deletion       : 0.00
% 3.86/1.67  Index Matching       : 0.00
% 3.86/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
