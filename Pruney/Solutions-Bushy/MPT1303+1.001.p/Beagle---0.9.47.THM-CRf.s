%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:45 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 178 expanded)
%              Number of leaves         :   24 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  128 ( 371 expanded)
%              Number of equality atoms :   22 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_99,plain,(
    ! [B_41] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_41,'#skF_6') = k3_xboole_0(B_41,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_34,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_34])).

tff(c_102,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    ! [B_43] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_43,'#skF_6') = k3_xboole_0(B_43,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k9_subset_1(A_19,B_20,C_21),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,(
    ! [B_43] :
      ( m1_subset_1(k3_xboole_0(B_43,'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_30])).

tff(c_117,plain,(
    ! [B_44] : m1_subset_1(k3_xboole_0(B_44,'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109])).

tff(c_123,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_6',A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_3,B_9] :
      ( m1_subset_1('#skF_1'(A_3,B_9),k1_zfmisc_1(u1_struct_0(A_3)))
      | v1_tops_2(B_9,A_3)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,(
    ! [B_49] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_49,'#skF_5') = k3_xboole_0(B_49,'#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_165,plain,(
    ! [B_49] :
      ( m1_subset_1(k3_xboole_0(B_49,'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_30])).

tff(c_171,plain,(
    ! [B_49] : m1_subset_1(k3_xboole_0(B_49,'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_264,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_59)
      | v1_tops_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58))))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_272,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0(B_49,'#skF_5')),k3_xboole_0(B_49,'#skF_5'))
      | v1_tops_2(k3_xboole_0(B_49,'#skF_5'),'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_171,c_264])).

tff(c_295,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0(B_49,'#skF_5')),k3_xboole_0(B_49,'#skF_5'))
      | v1_tops_2(k3_xboole_0(B_49,'#skF_5'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_272])).

tff(c_1789,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_hidden('#skF_2'(A_98,B_99,C_100),A_98)
      | r2_hidden('#skF_3'(A_98,B_99,C_100),C_100)
      | k3_xboole_0(A_98,B_99) = C_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( ~ r2_hidden('#skF_2'(A_13,B_14,C_15),C_15)
      | r2_hidden('#skF_3'(A_13,B_14,C_15),C_15)
      | k3_xboole_0(A_13,B_14) = C_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1810,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_3'(A_98,B_99,A_98),A_98)
      | k3_xboole_0(A_98,B_99) = A_98 ) ),
    inference(resolution,[status(thm)],[c_1789,c_24])).

tff(c_28,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_2'(A_13,B_14,C_15),A_13)
      | r2_hidden('#skF_3'(A_13,B_14,C_15),C_15)
      | k3_xboole_0(A_13,B_14) = C_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4746,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden('#skF_2'(A_145,B_146,C_147),A_145)
      | ~ r2_hidden('#skF_3'(A_145,B_146,C_147),B_146)
      | ~ r2_hidden('#skF_3'(A_145,B_146,C_147),A_145)
      | k3_xboole_0(A_145,B_146) = C_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5325,plain,(
    ! [A_159,C_160] :
      ( ~ r2_hidden('#skF_3'(A_159,C_160,C_160),A_159)
      | r2_hidden('#skF_2'(A_159,C_160,C_160),A_159)
      | k3_xboole_0(A_159,C_160) = C_160 ) ),
    inference(resolution,[status(thm)],[c_28,c_4746])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( ~ r2_hidden('#skF_2'(A_13,B_14,C_15),C_15)
      | ~ r2_hidden('#skF_3'(A_13,B_14,C_15),B_14)
      | ~ r2_hidden('#skF_3'(A_13,B_14,C_15),A_13)
      | k3_xboole_0(A_13,B_14) = C_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5378,plain,(
    ! [A_161] :
      ( ~ r2_hidden('#skF_3'(A_161,A_161,A_161),A_161)
      | k3_xboole_0(A_161,A_161) = A_161 ) ),
    inference(resolution,[status(thm)],[c_5325,c_18])).

tff(c_5399,plain,(
    ! [B_162] : k3_xboole_0(B_162,B_162) = B_162 ),
    inference(resolution,[status(thm)],[c_1810,c_5378])).

tff(c_144,plain,(
    ! [A_48] : m1_subset_1(k3_xboole_0('#skF_6',A_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24] :
      ( k9_subset_1(A_22,B_23,C_24) = k3_xboole_0(B_23,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2103,plain,(
    ! [B_114,A_115] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_114,k3_xboole_0('#skF_6',A_115)) = k3_xboole_0(B_114,k3_xboole_0('#skF_6',A_115)) ),
    inference(resolution,[status(thm)],[c_144,c_32])).

tff(c_200,plain,(
    ! [B_52,B_53] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_52,k3_xboole_0(B_53,'#skF_6')) = k3_xboole_0(B_52,k3_xboole_0(B_53,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_117,c_32])).

tff(c_213,plain,(
    ! [B_52,A_1] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_4')),B_52,k3_xboole_0('#skF_6',A_1)) = k3_xboole_0(B_52,k3_xboole_0(A_1,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_2159,plain,(
    ! [B_116,A_117] : k3_xboole_0(B_116,k3_xboole_0(A_117,'#skF_6')) = k3_xboole_0(B_116,k3_xboole_0('#skF_6',A_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2103,c_213])).

tff(c_14,plain,(
    ! [D_18,B_14,A_13] :
      ( r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2387,plain,(
    ! [D_18,A_117,B_116] :
      ( r2_hidden(D_18,k3_xboole_0(A_117,'#skF_6'))
      | ~ r2_hidden(D_18,k3_xboole_0(B_116,k3_xboole_0('#skF_6',A_117))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2159,c_14])).

tff(c_8162,plain,(
    ! [D_180,A_181] :
      ( r2_hidden(D_180,k3_xboole_0(A_181,'#skF_6'))
      | ~ r2_hidden(D_180,k3_xboole_0('#skF_6',A_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5399,c_2387])).

tff(c_8189,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),k3_xboole_0('#skF_5','#skF_6'))
    | v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_295,c_8162])).

tff(c_8243,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),k3_xboole_0('#skF_6','#skF_5'))
    | v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8189])).

tff(c_8244,plain,(
    r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_8243])).

tff(c_8559,plain,(
    r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8244,c_14])).

tff(c_4,plain,(
    ! [C_12,A_3,B_9] :
      ( v3_pre_topc(C_12,A_3)
      | ~ r2_hidden(C_12,B_9)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ v1_tops_2(B_9,A_3)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10507,plain,(
    ! [A_205] :
      ( v3_pre_topc('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),A_205)
      | ~ m1_subset_1('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ v1_tops_2('#skF_5',A_205)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_205))))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_8559,c_4])).

tff(c_10511,plain,
    ( v3_pre_topc('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),'#skF_4')
    | ~ v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_10507])).

tff(c_10514,plain,
    ( v3_pre_topc('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),'#skF_4')
    | v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_123,c_40,c_36,c_10511])).

tff(c_10515,plain,(
    v3_pre_topc('#skF_1'('#skF_4',k3_xboole_0('#skF_6','#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_10514])).

tff(c_6,plain,(
    ! [A_3,B_9] :
      ( ~ v3_pre_topc('#skF_1'(A_3,B_9),A_3)
      | v1_tops_2(B_9,A_3)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10517,plain,
    ( v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10515,c_6])).

tff(c_10520,plain,(
    v1_tops_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_123,c_10517])).

tff(c_10522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_10520])).

%------------------------------------------------------------------------------
