%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:49 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 102 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_45,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

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

tff(c_20,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_70,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [B_65,A_66,C_67] :
      ( v1_tops_2(B_65,A_66)
      | ~ v1_tops_2(C_67,A_66)
      | ~ r1_tarski(B_65,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_976,plain,(
    ! [A_126,B_127,A_128] :
      ( v1_tops_2(k4_xboole_0(A_126,B_127),A_128)
      | ~ v1_tops_2(A_126,A_128)
      | ~ m1_subset_1(A_126,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ m1_subset_1(k4_xboole_0(A_126,B_127),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128))))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_4,c_210])).

tff(c_1885,plain,(
    ! [A_184,B_185,A_186] :
      ( v1_tops_2(k4_xboole_0(A_184,B_185),A_186)
      | ~ v1_tops_2(A_184,A_186)
      | ~ m1_subset_1(A_184,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186))))
      | ~ l1_pre_topc(A_186)
      | ~ r1_tarski(k4_xboole_0(A_184,B_185),k1_zfmisc_1(u1_struct_0(A_186))) ) ),
    inference(resolution,[status(thm)],[c_14,c_976])).

tff(c_1937,plain,(
    ! [A_184,B_185] :
      ( v1_tops_2(k4_xboole_0(A_184,B_185),'#skF_1')
      | ~ v1_tops_2(A_184,'#skF_1')
      | ~ m1_subset_1(A_184,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k4_xboole_0(A_184,B_185),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_80,c_1885])).

tff(c_8016,plain,(
    ! [A_410,B_411] :
      ( v1_tops_2(k4_xboole_0(A_410,B_411),'#skF_1')
      | ~ v1_tops_2(A_410,'#skF_1')
      | ~ m1_subset_1(A_410,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k4_xboole_0(A_410,B_411),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1937])).

tff(c_8023,plain,(
    ! [B_411] :
      ( v1_tops_2(k4_xboole_0('#skF_2',B_411),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_411),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_8016])).

tff(c_8029,plain,(
    ! [B_412] : v1_tops_2(k4_xboole_0('#skF_2',B_412),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20,c_8023])).

tff(c_8053,plain,(
    ! [B_7] : v1_tops_2(k3_xboole_0('#skF_2',B_7),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_8029])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_97,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_45] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_45,'#skF_3') = k3_xboole_0(B_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_18,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_145,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_18])).

tff(c_8056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8053,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.41  
% 7.00/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.41  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 7.00/2.41  
% 7.00/2.41  %Foreground sorts:
% 7.00/2.41  
% 7.00/2.41  
% 7.00/2.41  %Background operators:
% 7.00/2.41  
% 7.00/2.41  
% 7.00/2.41  %Foreground operators:
% 7.00/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.00/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.00/2.41  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 7.00/2.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.00/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.00/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.00/2.41  tff('#skF_2', type, '#skF_2': $i).
% 7.00/2.41  tff('#skF_3', type, '#skF_3': $i).
% 7.00/2.41  tff('#skF_1', type, '#skF_1': $i).
% 7.00/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.00/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.00/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.00/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.00/2.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.00/2.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.00/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.00/2.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.00/2.41  
% 7.00/2.42  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.00/2.42  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.00/2.42  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 7.00/2.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.00/2.42  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.00/2.42  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 7.00/2.42  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.00/2.42  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.00/2.42  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.00/2.42  tff(c_20, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.00/2.42  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.00/2.42  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.00/2.42  tff(c_28, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.00/2.42  tff(c_36, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_28])).
% 7.00/2.42  tff(c_70, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.00/2.42  tff(c_80, plain, (![A_38]: (r1_tarski(A_38, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_70])).
% 7.00/2.42  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.00/2.42  tff(c_210, plain, (![B_65, A_66, C_67]: (v1_tops_2(B_65, A_66) | ~v1_tops_2(C_67, A_66) | ~r1_tarski(B_65, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66)))) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66)))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.00/2.42  tff(c_976, plain, (![A_126, B_127, A_128]: (v1_tops_2(k4_xboole_0(A_126, B_127), A_128) | ~v1_tops_2(A_126, A_128) | ~m1_subset_1(A_126, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128)))) | ~m1_subset_1(k4_xboole_0(A_126, B_127), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_128)))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_4, c_210])).
% 7.00/2.42  tff(c_1885, plain, (![A_184, B_185, A_186]: (v1_tops_2(k4_xboole_0(A_184, B_185), A_186) | ~v1_tops_2(A_184, A_186) | ~m1_subset_1(A_184, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186)))) | ~l1_pre_topc(A_186) | ~r1_tarski(k4_xboole_0(A_184, B_185), k1_zfmisc_1(u1_struct_0(A_186))))), inference(resolution, [status(thm)], [c_14, c_976])).
% 7.00/2.42  tff(c_1937, plain, (![A_184, B_185]: (v1_tops_2(k4_xboole_0(A_184, B_185), '#skF_1') | ~v1_tops_2(A_184, '#skF_1') | ~m1_subset_1(A_184, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k4_xboole_0(A_184, B_185), '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_1885])).
% 7.00/2.42  tff(c_8016, plain, (![A_410, B_411]: (v1_tops_2(k4_xboole_0(A_410, B_411), '#skF_1') | ~v1_tops_2(A_410, '#skF_1') | ~m1_subset_1(A_410, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(k4_xboole_0(A_410, B_411), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1937])).
% 7.00/2.42  tff(c_8023, plain, (![B_411]: (v1_tops_2(k4_xboole_0('#skF_2', B_411), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', B_411), '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_8016])).
% 7.00/2.42  tff(c_8029, plain, (![B_412]: (v1_tops_2(k4_xboole_0('#skF_2', B_412), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20, c_8023])).
% 7.00/2.42  tff(c_8053, plain, (![B_7]: (v1_tops_2(k3_xboole_0('#skF_2', B_7), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_8029])).
% 7.00/2.42  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.00/2.42  tff(c_97, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.00/2.42  tff(c_105, plain, (![B_45]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_45, '#skF_3')=k3_xboole_0(B_45, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_97])).
% 7.00/2.42  tff(c_18, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.00/2.42  tff(c_145, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_18])).
% 7.00/2.42  tff(c_8056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8053, c_145])).
% 7.00/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.42  
% 7.00/2.42  Inference rules
% 7.00/2.42  ----------------------
% 7.00/2.42  #Ref     : 0
% 7.00/2.42  #Sup     : 1861
% 7.00/2.42  #Fact    : 0
% 7.00/2.42  #Define  : 0
% 7.00/2.42  #Split   : 2
% 7.00/2.42  #Chain   : 0
% 7.00/2.42  #Close   : 0
% 7.00/2.42  
% 7.00/2.42  Ordering : KBO
% 7.00/2.42  
% 7.00/2.42  Simplification rules
% 7.00/2.42  ----------------------
% 7.00/2.42  #Subsume      : 174
% 7.00/2.42  #Demod        : 478
% 7.00/2.42  #Tautology    : 439
% 7.00/2.42  #SimpNegUnit  : 0
% 7.00/2.42  #BackRed      : 2
% 7.00/2.42  
% 7.00/2.42  #Partial instantiations: 0
% 7.00/2.42  #Strategies tried      : 1
% 7.00/2.42  
% 7.00/2.42  Timing (in seconds)
% 7.00/2.42  ----------------------
% 7.00/2.43  Preprocessing        : 0.31
% 7.00/2.43  Parsing              : 0.17
% 7.00/2.43  CNF conversion       : 0.02
% 7.00/2.43  Main loop            : 1.37
% 7.00/2.43  Inferencing          : 0.42
% 7.00/2.43  Reduction            : 0.46
% 7.00/2.43  Demodulation         : 0.37
% 7.00/2.43  BG Simplification    : 0.05
% 7.00/2.43  Subsumption          : 0.34
% 7.00/2.43  Abstraction          : 0.06
% 7.00/2.43  MUC search           : 0.00
% 7.00/2.43  Cooper               : 0.00
% 7.00/2.43  Total                : 1.70
% 7.00/2.43  Index Insertion      : 0.00
% 7.00/2.43  Index Deletion       : 0.00
% 7.00/2.43  Index Matching       : 0.00
% 7.00/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
