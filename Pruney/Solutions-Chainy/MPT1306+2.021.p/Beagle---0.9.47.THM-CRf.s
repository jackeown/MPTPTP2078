%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:54 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 102 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_26])).

tff(c_59,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_34,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [B_61,A_62,C_63] :
      ( v2_tops_2(B_61,A_62)
      | ~ v2_tops_2(C_63,A_62)
      | ~ r1_tarski(B_61,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_999,plain,(
    ! [A_126,B_127,A_128] :
      ( v2_tops_2(k4_xboole_0(A_126,B_127),A_128)
      | ~ v2_tops_2(A_126,A_128)
      | ~ m1_subset_1(A_126,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ m1_subset_1(k4_xboole_0(A_126,B_127),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_2120,plain,(
    ! [A_197,B_198,A_199] :
      ( v2_tops_2(k4_xboole_0(A_197,B_198),A_199)
      | ~ v2_tops_2(A_197,A_199)
      | ~ m1_subset_1(A_197,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_199))))
      | ~ l1_pre_topc(A_199)
      | ~ r1_tarski(k4_xboole_0(A_197,B_198),k1_zfmisc_1(u1_struct_0(A_199))) ) ),
    inference(resolution,[status(thm)],[c_12,c_999])).

tff(c_2172,plain,(
    ! [A_197,B_198] :
      ( v2_tops_2(k4_xboole_0(A_197,B_198),'#skF_1')
      | ~ v2_tops_2(A_197,'#skF_1')
      | ~ m1_subset_1(A_197,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k4_xboole_0(A_197,B_198),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_69,c_2120])).

tff(c_7976,plain,(
    ! [A_406,B_407] :
      ( v2_tops_2(k4_xboole_0(A_406,B_407),'#skF_1')
      | ~ v2_tops_2(A_406,'#skF_1')
      | ~ m1_subset_1(A_406,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k4_xboole_0(A_406,B_407),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2172])).

tff(c_7983,plain,(
    ! [B_407] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_407),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_407),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_7976])).

tff(c_7989,plain,(
    ! [B_408] : v2_tops_2(k4_xboole_0('#skF_2',B_408),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_7983])).

tff(c_8013,plain,(
    ! [B_7] : v2_tops_2(k3_xboole_0('#skF_2',B_7),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7989])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,(
    ! [A_43,B_44,C_45] :
      ( k9_subset_1(A_43,B_44,C_45) = k3_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [B_44] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_44,'#skF_3') = k3_xboole_0(B_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_16,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_148,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_16])).

tff(c_8016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8013,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:56:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.62  
% 7.31/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.62  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.31/2.62  
% 7.31/2.62  %Foreground sorts:
% 7.31/2.62  
% 7.31/2.62  
% 7.31/2.62  %Background operators:
% 7.31/2.62  
% 7.31/2.62  
% 7.31/2.62  %Foreground operators:
% 7.31/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.31/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.62  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.62  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.62  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.62  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 7.31/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.31/2.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.31/2.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.62  
% 7.31/2.63  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.31/2.63  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.31/2.63  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tops_2)).
% 7.31/2.63  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.31/2.63  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.31/2.63  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 7.31/2.63  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.31/2.63  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.63  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.31/2.63  tff(c_18, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.63  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.63  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.63  tff(c_26, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.63  tff(c_34, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_26])).
% 7.31/2.63  tff(c_59, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.63  tff(c_69, plain, (![A_34]: (r1_tarski(A_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_34, '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_59])).
% 7.31/2.63  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.63  tff(c_199, plain, (![B_61, A_62, C_63]: (v2_tops_2(B_61, A_62) | ~v2_tops_2(C_63, A_62) | ~r1_tarski(B_61, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.31/2.63  tff(c_999, plain, (![A_126, B_127, A_128]: (v2_tops_2(k4_xboole_0(A_126, B_127), A_128) | ~v2_tops_2(A_126, A_128) | ~m1_subset_1(A_126, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128)))) | ~m1_subset_1(k4_xboole_0(A_126, B_127), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128)))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_4, c_199])).
% 7.31/2.63  tff(c_2120, plain, (![A_197, B_198, A_199]: (v2_tops_2(k4_xboole_0(A_197, B_198), A_199) | ~v2_tops_2(A_197, A_199) | ~m1_subset_1(A_197, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_199)))) | ~l1_pre_topc(A_199) | ~r1_tarski(k4_xboole_0(A_197, B_198), k1_zfmisc_1(u1_struct_0(A_199))))), inference(resolution, [status(thm)], [c_12, c_999])).
% 7.31/2.63  tff(c_2172, plain, (![A_197, B_198]: (v2_tops_2(k4_xboole_0(A_197, B_198), '#skF_1') | ~v2_tops_2(A_197, '#skF_1') | ~m1_subset_1(A_197, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k4_xboole_0(A_197, B_198), '#skF_2'))), inference(resolution, [status(thm)], [c_69, c_2120])).
% 7.31/2.63  tff(c_7976, plain, (![A_406, B_407]: (v2_tops_2(k4_xboole_0(A_406, B_407), '#skF_1') | ~v2_tops_2(A_406, '#skF_1') | ~m1_subset_1(A_406, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(k4_xboole_0(A_406, B_407), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2172])).
% 7.31/2.63  tff(c_7983, plain, (![B_407]: (v2_tops_2(k4_xboole_0('#skF_2', B_407), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', B_407), '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_7976])).
% 7.31/2.63  tff(c_7989, plain, (![B_408]: (v2_tops_2(k4_xboole_0('#skF_2', B_408), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_7983])).
% 7.31/2.63  tff(c_8013, plain, (![B_7]: (v2_tops_2(k3_xboole_0('#skF_2', B_7), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7989])).
% 7.31/2.63  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.63  tff(c_98, plain, (![A_43, B_44, C_45]: (k9_subset_1(A_43, B_44, C_45)=k3_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.63  tff(c_106, plain, (![B_44]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_44, '#skF_3')=k3_xboole_0(B_44, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_98])).
% 7.31/2.63  tff(c_16, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.63  tff(c_148, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_16])).
% 7.31/2.63  tff(c_8016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8013, c_148])).
% 7.31/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.63  
% 7.31/2.63  Inference rules
% 7.31/2.63  ----------------------
% 7.31/2.63  #Ref     : 0
% 7.31/2.63  #Sup     : 1855
% 7.31/2.63  #Fact    : 0
% 7.31/2.63  #Define  : 0
% 7.31/2.63  #Split   : 2
% 7.31/2.63  #Chain   : 0
% 7.31/2.63  #Close   : 0
% 7.31/2.63  
% 7.31/2.63  Ordering : KBO
% 7.31/2.63  
% 7.31/2.63  Simplification rules
% 7.31/2.63  ----------------------
% 7.31/2.63  #Subsume      : 168
% 7.31/2.63  #Demod        : 457
% 7.31/2.63  #Tautology    : 416
% 7.31/2.63  #SimpNegUnit  : 0
% 7.31/2.63  #BackRed      : 2
% 7.31/2.63  
% 7.31/2.63  #Partial instantiations: 0
% 7.31/2.63  #Strategies tried      : 1
% 7.31/2.63  
% 7.31/2.63  Timing (in seconds)
% 7.31/2.63  ----------------------
% 7.31/2.63  Preprocessing        : 0.31
% 7.31/2.63  Parsing              : 0.17
% 7.31/2.63  CNF conversion       : 0.02
% 7.31/2.63  Main loop            : 1.57
% 7.31/2.63  Inferencing          : 0.47
% 7.31/2.63  Reduction            : 0.54
% 7.31/2.63  Demodulation         : 0.44
% 7.31/2.63  BG Simplification    : 0.06
% 7.31/2.63  Subsumption          : 0.39
% 7.31/2.63  Abstraction          : 0.07
% 7.31/2.63  MUC search           : 0.00
% 7.31/2.63  Cooper               : 0.00
% 7.31/2.63  Total                : 1.90
% 7.31/2.64  Index Insertion      : 0.00
% 7.31/2.64  Index Deletion       : 0.00
% 7.31/2.64  Index Matching       : 0.00
% 7.31/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
