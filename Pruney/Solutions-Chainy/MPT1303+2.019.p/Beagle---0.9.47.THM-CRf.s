%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:49 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 (  93 expanded)
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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_49,A_50,C_51] :
      ( v1_tops_2(B_49,A_50)
      | ~ v1_tops_2(C_51,A_50)
      | ~ r1_tarski(B_49,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_190,plain,(
    ! [A_63,B_64,A_65] :
      ( v1_tops_2(k4_xboole_0(A_63,B_64),A_65)
      | ~ v1_tops_2(A_63,A_65)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ m1_subset_1(k4_xboole_0(A_63,B_64),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_579,plain,(
    ! [A_93,B_94,A_95] :
      ( v1_tops_2(k4_xboole_0(A_93,B_94),A_95)
      | ~ v1_tops_2(A_93,A_95)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ l1_pre_topc(A_95)
      | ~ r1_tarski(k4_xboole_0(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_95))) ) ),
    inference(resolution,[status(thm)],[c_14,c_190])).

tff(c_1043,plain,(
    ! [A_134,C_135,A_136] :
      ( v1_tops_2(k4_xboole_0(A_134,C_135),A_136)
      | ~ v1_tops_2(A_134,A_136)
      | ~ m1_subset_1(A_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_136))))
      | ~ l1_pre_topc(A_136)
      | ~ r1_tarski(A_134,k1_zfmisc_1(u1_struct_0(A_136))) ) ),
    inference(resolution,[status(thm)],[c_2,c_579])).

tff(c_1050,plain,(
    ! [C_135] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_135),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_1043])).

tff(c_1058,plain,(
    ! [C_137] : v1_tops_2(k4_xboole_0('#skF_2',C_137),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_20,c_1050])).

tff(c_1086,plain,(
    ! [B_7] : v1_tops_2(k3_xboole_0('#skF_2',B_7),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1058])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_45] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_45,'#skF_3') = k3_xboole_0(B_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_18,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_18])).

tff(c_1089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.51  
% 3.48/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.51  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.51  
% 3.48/1.51  %Foreground sorts:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Background operators:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Foreground operators:
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.51  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.48/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.48/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.51  
% 3.48/1.53  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.48/1.53  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 3.48/1.53  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.53  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.48/1.53  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.48/1.53  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 3.48/1.53  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.48/1.53  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.53  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.53  tff(c_28, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.53  tff(c_36, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_28])).
% 3.48/1.53  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.53  tff(c_20, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.53  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.53  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.53  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.53  tff(c_104, plain, (![B_49, A_50, C_51]: (v1_tops_2(B_49, A_50) | ~v1_tops_2(C_51, A_50) | ~r1_tarski(B_49, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.48/1.53  tff(c_190, plain, (![A_63, B_64, A_65]: (v1_tops_2(k4_xboole_0(A_63, B_64), A_65) | ~v1_tops_2(A_63, A_65) | ~m1_subset_1(A_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~m1_subset_1(k4_xboole_0(A_63, B_64), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_4, c_104])).
% 3.48/1.53  tff(c_579, plain, (![A_93, B_94, A_95]: (v1_tops_2(k4_xboole_0(A_93, B_94), A_95) | ~v1_tops_2(A_93, A_95) | ~m1_subset_1(A_93, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~l1_pre_topc(A_95) | ~r1_tarski(k4_xboole_0(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_95))))), inference(resolution, [status(thm)], [c_14, c_190])).
% 3.48/1.53  tff(c_1043, plain, (![A_134, C_135, A_136]: (v1_tops_2(k4_xboole_0(A_134, C_135), A_136) | ~v1_tops_2(A_134, A_136) | ~m1_subset_1(A_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_136)))) | ~l1_pre_topc(A_136) | ~r1_tarski(A_134, k1_zfmisc_1(u1_struct_0(A_136))))), inference(resolution, [status(thm)], [c_2, c_579])).
% 3.48/1.53  tff(c_1050, plain, (![C_135]: (v1_tops_2(k4_xboole_0('#skF_2', C_135), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_24, c_1043])).
% 3.48/1.53  tff(c_1058, plain, (![C_137]: (v1_tops_2(k4_xboole_0('#skF_2', C_137), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_20, c_1050])).
% 3.48/1.53  tff(c_1086, plain, (![B_7]: (v1_tops_2(k3_xboole_0('#skF_2', B_7), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1058])).
% 3.48/1.53  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.53  tff(c_75, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.53  tff(c_83, plain, (![B_45]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_45, '#skF_3')=k3_xboole_0(B_45, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_75])).
% 3.48/1.53  tff(c_18, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.53  tff(c_85, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_18])).
% 3.48/1.53  tff(c_1089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1086, c_85])).
% 3.48/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.53  
% 3.48/1.53  Inference rules
% 3.48/1.53  ----------------------
% 3.48/1.53  #Ref     : 0
% 3.48/1.53  #Sup     : 257
% 3.48/1.53  #Fact    : 0
% 3.48/1.53  #Define  : 0
% 3.48/1.53  #Split   : 4
% 3.48/1.53  #Chain   : 0
% 3.48/1.53  #Close   : 0
% 3.48/1.53  
% 3.48/1.53  Ordering : KBO
% 3.48/1.53  
% 3.48/1.53  Simplification rules
% 3.48/1.53  ----------------------
% 3.48/1.53  #Subsume      : 58
% 3.48/1.53  #Demod        : 237
% 3.48/1.53  #Tautology    : 74
% 3.48/1.53  #SimpNegUnit  : 0
% 3.48/1.53  #BackRed      : 2
% 3.48/1.53  
% 3.48/1.53  #Partial instantiations: 0
% 3.48/1.53  #Strategies tried      : 1
% 3.48/1.53  
% 3.48/1.53  Timing (in seconds)
% 3.48/1.53  ----------------------
% 3.48/1.53  Preprocessing        : 0.29
% 3.48/1.53  Parsing              : 0.16
% 3.48/1.53  CNF conversion       : 0.02
% 3.48/1.53  Main loop            : 0.47
% 3.48/1.53  Inferencing          : 0.17
% 3.48/1.53  Reduction            : 0.17
% 3.48/1.53  Demodulation         : 0.13
% 3.48/1.53  BG Simplification    : 0.02
% 3.48/1.53  Subsumption          : 0.08
% 3.48/1.53  Abstraction          : 0.03
% 3.48/1.53  MUC search           : 0.00
% 3.48/1.53  Cooper               : 0.00
% 3.48/1.53  Total                : 0.79
% 3.48/1.53  Index Insertion      : 0.00
% 3.48/1.53  Index Deletion       : 0.00
% 3.48/1.53  Index Matching       : 0.00
% 3.48/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
