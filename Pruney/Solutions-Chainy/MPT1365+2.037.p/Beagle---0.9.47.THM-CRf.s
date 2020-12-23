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
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 108 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 350 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_123,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_22])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | ~ v2_compts_1(B_64,A_65)
      | ~ v8_pre_topc(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_169,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_162])).

tff(c_24,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_165,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_172,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_24,c_165])).

tff(c_349,plain,(
    ! [A_87,B_88,C_89] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_87),B_88,C_89),A_87)
      | ~ v4_pre_topc(C_89,A_87)
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_368,plain,(
    ! [B_57] :
      ( v4_pre_topc(k3_xboole_0(B_57,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_57,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_349])).

tff(c_376,plain,(
    ! [B_90] :
      ( v4_pre_topc(k3_xboole_0(B_90,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_90,'#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_172,c_368])).

tff(c_383,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_376])).

tff(c_390,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_383])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

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

tff(c_182,plain,(
    ! [C_69,A_70,B_71] :
      ( v2_compts_1(C_69,A_70)
      | ~ v4_pre_topc(C_69,A_70)
      | ~ r1_tarski(C_69,B_71)
      | ~ v2_compts_1(B_71,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_609,plain,(
    ! [A_106,B_107,A_108] :
      ( v2_compts_1(k4_xboole_0(A_106,B_107),A_108)
      | ~ v4_pre_topc(k4_xboole_0(A_106,B_107),A_108)
      | ~ v2_compts_1(A_106,A_108)
      | ~ m1_subset_1(k4_xboole_0(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(A_106,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_4,c_182])).

tff(c_995,plain,(
    ! [A_127,B_128,A_129] :
      ( v2_compts_1(k4_xboole_0(A_127,B_128),A_129)
      | ~ v4_pre_topc(k4_xboole_0(A_127,B_128),A_129)
      | ~ v2_compts_1(A_127,A_129)
      | ~ m1_subset_1(A_127,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | ~ r1_tarski(k4_xboole_0(A_127,B_128),u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_14,c_609])).

tff(c_1043,plain,(
    ! [A_130,C_131,A_132] :
      ( v2_compts_1(k4_xboole_0(A_130,C_131),A_132)
      | ~ v4_pre_topc(k4_xboole_0(A_130,C_131),A_132)
      | ~ v2_compts_1(A_130,A_132)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | ~ r1_tarski(A_130,u1_struct_0(A_132)) ) ),
    inference(resolution,[status(thm)],[c_2,c_995])).

tff(c_1065,plain,(
    ! [A_6,B_7,A_132] :
      ( v2_compts_1(k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)),A_132)
      | ~ v4_pre_topc(k3_xboole_0(A_6,B_7),A_132)
      | ~ v2_compts_1(A_6,A_132)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | ~ r1_tarski(A_6,u1_struct_0(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1043])).

tff(c_1223,plain,(
    ! [A_137,B_138,A_139] :
      ( v2_compts_1(k3_xboole_0(A_137,B_138),A_139)
      | ~ v4_pre_topc(k3_xboole_0(A_137,B_138),A_139)
      | ~ v2_compts_1(A_137,A_139)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | ~ r1_tarski(A_137,u1_struct_0(A_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1065])).

tff(c_1239,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_390,c_1223])).

tff(c_1259,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_36,c_34,c_32,c_26,c_1239])).

tff(c_1261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:40:31 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.58  
% 3.66/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.58  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.58  
% 3.66/1.58  %Foreground sorts:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Background operators:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Foreground operators:
% 3.66/1.58  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.66/1.58  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.66/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.66/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.66/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.66/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.66/1.58  
% 3.66/1.60  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 3.66/1.60  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.66/1.60  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.66/1.60  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 3.66/1.60  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 3.66/1.60  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.66/1.60  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.66/1.60  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.66/1.60  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 3.66/1.60  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_104, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.60  tff(c_113, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), B_57, '#skF_3')=k3_xboole_0(B_57, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_104])).
% 3.66/1.60  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_123, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_22])).
% 3.66/1.60  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_38, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.60  tff(c_45, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 3.66/1.60  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_155, plain, (![B_64, A_65]: (v4_pre_topc(B_64, A_65) | ~v2_compts_1(B_64, A_65) | ~v8_pre_topc(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.66/1.60  tff(c_162, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_155])).
% 3.66/1.60  tff(c_169, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_162])).
% 3.66/1.60  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.66/1.60  tff(c_165, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_155])).
% 3.66/1.60  tff(c_172, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_165])).
% 3.66/1.60  tff(c_349, plain, (![A_87, B_88, C_89]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_87), B_88, C_89), A_87) | ~v4_pre_topc(C_89, A_87) | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.60  tff(c_368, plain, (![B_57]: (v4_pre_topc(k3_xboole_0(B_57, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_57, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_349])).
% 3.66/1.60  tff(c_376, plain, (![B_90]: (v4_pre_topc(k3_xboole_0(B_90, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_90, '#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_172, c_368])).
% 3.66/1.60  tff(c_383, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_376])).
% 3.66/1.60  tff(c_390, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_383])).
% 3.66/1.60  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.66/1.60  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.60  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.60  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.60  tff(c_182, plain, (![C_69, A_70, B_71]: (v2_compts_1(C_69, A_70) | ~v4_pre_topc(C_69, A_70) | ~r1_tarski(C_69, B_71) | ~v2_compts_1(B_71, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.60  tff(c_609, plain, (![A_106, B_107, A_108]: (v2_compts_1(k4_xboole_0(A_106, B_107), A_108) | ~v4_pre_topc(k4_xboole_0(A_106, B_107), A_108) | ~v2_compts_1(A_106, A_108) | ~m1_subset_1(k4_xboole_0(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(A_106, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(resolution, [status(thm)], [c_4, c_182])).
% 3.66/1.60  tff(c_995, plain, (![A_127, B_128, A_129]: (v2_compts_1(k4_xboole_0(A_127, B_128), A_129) | ~v4_pre_topc(k4_xboole_0(A_127, B_128), A_129) | ~v2_compts_1(A_127, A_129) | ~m1_subset_1(A_127, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | ~r1_tarski(k4_xboole_0(A_127, B_128), u1_struct_0(A_129)))), inference(resolution, [status(thm)], [c_14, c_609])).
% 3.66/1.60  tff(c_1043, plain, (![A_130, C_131, A_132]: (v2_compts_1(k4_xboole_0(A_130, C_131), A_132) | ~v4_pre_topc(k4_xboole_0(A_130, C_131), A_132) | ~v2_compts_1(A_130, A_132) | ~m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | ~r1_tarski(A_130, u1_struct_0(A_132)))), inference(resolution, [status(thm)], [c_2, c_995])).
% 3.66/1.60  tff(c_1065, plain, (![A_6, B_7, A_132]: (v2_compts_1(k4_xboole_0(A_6, k4_xboole_0(A_6, B_7)), A_132) | ~v4_pre_topc(k3_xboole_0(A_6, B_7), A_132) | ~v2_compts_1(A_6, A_132) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | ~r1_tarski(A_6, u1_struct_0(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1043])).
% 3.66/1.60  tff(c_1223, plain, (![A_137, B_138, A_139]: (v2_compts_1(k3_xboole_0(A_137, B_138), A_139) | ~v4_pre_topc(k3_xboole_0(A_137, B_138), A_139) | ~v2_compts_1(A_137, A_139) | ~m1_subset_1(A_137, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | ~r1_tarski(A_137, u1_struct_0(A_139)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1065])).
% 3.66/1.60  tff(c_1239, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_390, c_1223])).
% 3.66/1.60  tff(c_1259, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_36, c_34, c_32, c_26, c_1239])).
% 3.66/1.60  tff(c_1261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1259])).
% 3.66/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.60  
% 3.66/1.60  Inference rules
% 3.66/1.60  ----------------------
% 3.66/1.60  #Ref     : 0
% 3.66/1.60  #Sup     : 300
% 3.66/1.60  #Fact    : 0
% 3.66/1.60  #Define  : 0
% 3.66/1.60  #Split   : 0
% 3.66/1.60  #Chain   : 0
% 3.66/1.60  #Close   : 0
% 3.66/1.60  
% 3.66/1.60  Ordering : KBO
% 3.66/1.60  
% 3.66/1.60  Simplification rules
% 3.66/1.60  ----------------------
% 3.66/1.60  #Subsume      : 37
% 3.66/1.60  #Demod        : 530
% 3.66/1.60  #Tautology    : 122
% 3.66/1.60  #SimpNegUnit  : 1
% 3.66/1.60  #BackRed      : 1
% 3.66/1.60  
% 3.66/1.60  #Partial instantiations: 0
% 3.66/1.60  #Strategies tried      : 1
% 3.66/1.60  
% 3.66/1.60  Timing (in seconds)
% 3.66/1.60  ----------------------
% 3.66/1.60  Preprocessing        : 0.31
% 3.66/1.60  Parsing              : 0.17
% 3.66/1.60  CNF conversion       : 0.02
% 3.66/1.60  Main loop            : 0.53
% 3.66/1.60  Inferencing          : 0.19
% 3.66/1.60  Reduction            : 0.21
% 3.66/1.60  Demodulation         : 0.16
% 3.66/1.60  BG Simplification    : 0.03
% 3.66/1.60  Subsumption          : 0.08
% 3.66/1.60  Abstraction          : 0.03
% 3.66/1.60  MUC search           : 0.00
% 3.66/1.60  Cooper               : 0.00
% 3.66/1.60  Total                : 0.87
% 3.66/1.60  Index Insertion      : 0.00
% 3.66/1.60  Index Deletion       : 0.00
% 3.66/1.60  Index Matching       : 0.00
% 3.66/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
