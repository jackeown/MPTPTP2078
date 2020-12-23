%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:51 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 178 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > m1_subset_1 > l1_pre_topc > k4_subset_1 > k7_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( v2_tops_2(B,A)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => k7_setfam_1(A,k4_subset_1(k1_zfmisc_1(A),B,C)) = k4_subset_1(k1_zfmisc_1(A),k7_setfam_1(A,B),k7_setfam_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_setfam_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( v1_tops_2(B,A)
                  & v1_tops_2(C,A) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tops_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_31,B_32] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_31),B_32),A_31)
      | ~ v2_tops_2(B_32,A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_46,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_38])).

tff(c_16,plain,(
    v2_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v2_tops_2('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_28])).

tff(c_43,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_36])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k7_setfam_1(A_4,B_5),k1_zfmisc_1(k1_zfmisc_1(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k4_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_7,C_9] :
      ( k4_subset_1(k1_zfmisc_1(A_6),k7_setfam_1(A_6,B_7),k7_setfam_1(A_6,C_9)) = k7_setfam_1(A_6,k4_subset_1(k1_zfmisc_1(A_6),B_7,C_9))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    ! [A_38,B_39,C_40] :
      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_38)),B_39,C_40),A_38)
      | ~ v1_tops_2(C_40,A_38)
      | ~ v1_tops_2(B_39,A_38)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [A_47,B_48,C_49] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_47),k4_subset_1(k1_zfmisc_1(u1_struct_0(A_47)),B_48,C_49)),A_47)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_47),C_49),A_47)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_47),B_48),A_47)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_47),C_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_47),B_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47))))
      | ~ l1_pre_topc(A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47))))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_8,plain,(
    ! [B_12,A_10] :
      ( v2_tops_2(B_12,A_10)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [A_59,B_60,C_61] :
      ( v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_59)),B_60,C_61),A_59)
      | ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_59)),B_60,C_61),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_59),C_61),A_59)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_59),B_60),A_59)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_59),C_61),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_59),B_60),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_pre_topc(A_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) ) ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_133,plain,(
    ! [A_62,B_63,C_64] :
      ( v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_62)),B_63,C_64),A_62)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_62),C_64),A_62)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_62),B_63),A_62)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_62),C_64),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_62),B_63),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_146,plain,(
    ! [A_65,B_66,B_67] :
      ( v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_65)),B_66,B_67),A_65)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_65),B_67),A_65)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_65),B_66),A_65)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_65),B_66),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ l1_pre_topc(A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_159,plain,(
    ! [A_68,B_69,B_70] :
      ( v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_68)),B_69,B_70),A_68)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_68),B_70),A_68)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_68),B_69),A_68)
      | ~ l1_pre_topc(A_68)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))) ) ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_14,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_166,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_159,c_14])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_46,c_43,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.28  % Computer   : n017.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % DateTime   : Tue Dec  1 12:54:16 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  %$ v2_tops_2 > v1_tops_2 > m1_subset_1 > l1_pre_topc > k4_subset_1 > k7_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.28  
% 2.24/1.28  %Foreground sorts:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Background operators:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Foreground operators:
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.28  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.24/1.28  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.24/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.24/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.28  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.28  
% 2.24/1.29  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((v2_tops_2(B, A) & v2_tops_2(C, A)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tops_2)).
% 2.24/1.29  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 2.24/1.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.24/1.29  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.24/1.29  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k4_subset_1(k1_zfmisc_1(A), B, C)) = k4_subset_1(k1_zfmisc_1(A), k7_setfam_1(A, B), k7_setfam_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_setfam_1)).
% 2.24/1.29  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((v1_tops_2(B, A) & v1_tops_2(C, A)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tops_2)).
% 2.24/1.29  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_18, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_28, plain, (![A_31, B_32]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_31), B_32), A_31) | ~v2_tops_2(B_32, A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31)))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.29  tff(c_38, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.24/1.29  tff(c_46, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_38])).
% 2.24/1.29  tff(c_16, plain, (v2_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_36, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v2_tops_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_28])).
% 2.24/1.29  tff(c_43, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_36])).
% 2.24/1.29  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k7_setfam_1(A_4, B_5), k1_zfmisc_1(k1_zfmisc_1(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.29  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k4_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.29  tff(c_6, plain, (![A_6, B_7, C_9]: (k4_subset_1(k1_zfmisc_1(A_6), k7_setfam_1(A_6, B_7), k7_setfam_1(A_6, C_9))=k7_setfam_1(A_6, k4_subset_1(k1_zfmisc_1(A_6), B_7, C_9)) | ~m1_subset_1(C_9, k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.29  tff(c_73, plain, (![A_38, B_39, C_40]: (v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_38)), B_39, C_40), A_38) | ~v1_tops_2(C_40, A_38) | ~v1_tops_2(B_39, A_38) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.29  tff(c_94, plain, (![A_47, B_48, C_49]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_47), k4_subset_1(k1_zfmisc_1(u1_struct_0(A_47)), B_48, C_49)), A_47) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_47), C_49), A_47) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_47), B_48), A_47) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_47), C_49), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_47), B_48), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47)))) | ~l1_pre_topc(A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47)))) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_47)))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 2.24/1.29  tff(c_8, plain, (![B_12, A_10]: (v2_tops_2(B_12, A_10) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.29  tff(c_123, plain, (![A_59, B_60, C_61]: (v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_59)), B_60, C_61), A_59) | ~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_59)), B_60, C_61), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_59), C_61), A_59) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_59), B_60), A_59) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_59), C_61), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_59), B_60), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_pre_topc(A_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))))), inference(resolution, [status(thm)], [c_94, c_8])).
% 2.24/1.29  tff(c_133, plain, (![A_62, B_63, C_64]: (v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_62)), B_63, C_64), A_62) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_62), C_64), A_62) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_62), B_63), A_62) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_62), C_64), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_62), B_63), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~l1_pre_topc(A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))))), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.24/1.29  tff(c_146, plain, (![A_65, B_66, B_67]: (v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_65)), B_66, B_67), A_65) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_65), B_67), A_65) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_65), B_66), A_65) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_65), B_66), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~l1_pre_topc(A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.24/1.29  tff(c_159, plain, (![A_68, B_69, B_70]: (v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(A_68)), B_69, B_70), A_68) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_68), B_70), A_68) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_68), B_69), A_68) | ~l1_pre_topc(A_68) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))))), inference(resolution, [status(thm)], [c_4, c_146])).
% 2.24/1.29  tff(c_14, plain, (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.24/1.29  tff(c_166, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_159, c_14])).
% 2.24/1.29  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_46, c_43, c_166])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 33
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 0
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 4
% 2.24/1.29  #Demod        : 15
% 2.24/1.29  #Tautology    : 7
% 2.24/1.29  #SimpNegUnit  : 0
% 2.24/1.29  #BackRed      : 0
% 2.24/1.29  
% 2.24/1.29  #Partial instantiations: 0
% 2.24/1.29  #Strategies tried      : 1
% 2.24/1.29  
% 2.24/1.29  Timing (in seconds)
% 2.24/1.29  ----------------------
% 2.24/1.30  Preprocessing        : 0.34
% 2.24/1.30  Parsing              : 0.18
% 2.24/1.30  CNF conversion       : 0.02
% 2.24/1.30  Main loop            : 0.25
% 2.24/1.30  Inferencing          : 0.11
% 2.24/1.30  Reduction            : 0.07
% 2.24/1.30  Demodulation         : 0.05
% 2.24/1.30  BG Simplification    : 0.02
% 2.24/1.30  Subsumption          : 0.05
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.62
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
