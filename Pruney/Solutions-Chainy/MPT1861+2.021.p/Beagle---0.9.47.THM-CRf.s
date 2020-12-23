%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 314 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1443,plain,(
    ! [A_112,B_113,C_114] :
      ( k9_subset_1(A_112,B_113,C_114) = k3_xboole_0(B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1448,plain,(
    ! [B_113] : k9_subset_1(u1_struct_0('#skF_1'),B_113,'#skF_3') = k3_xboole_0(B_113,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1443])).

tff(c_1491,plain,(
    ! [A_122,C_123,B_124] :
      ( k9_subset_1(A_122,C_123,B_124) = k9_subset_1(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1499,plain,(
    ! [B_124] : k9_subset_1(u1_struct_0('#skF_1'),B_124,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_124) ),
    inference(resolution,[status(thm)],[c_18,c_1491])).

tff(c_1509,plain,(
    ! [B_125] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_125) = k3_xboole_0(B_125,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1499])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1449,plain,(
    ! [B_113] : k9_subset_1(u1_struct_0('#skF_1'),B_113,'#skF_2') = k3_xboole_0(B_113,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1443])).

tff(c_1516,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_1449])).

tff(c_14,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1450,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_14])).

tff(c_1540,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1450])).

tff(c_35,plain,(
    ! [A_32,B_33,C_34] :
      ( k9_subset_1(A_32,B_33,C_34) = k3_xboole_0(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [B_33] : k9_subset_1(u1_struct_0('#skF_1'),B_33,'#skF_3') = k3_xboole_0(B_33,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_82,plain,(
    ! [A_39,C_40,B_41] :
      ( k9_subset_1(A_39,C_40,B_41) = k9_subset_1(A_39,B_41,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_41) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_100,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_42) = k3_xboole_0(B_42,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_90])).

tff(c_44,plain,(
    ! [B_33] : k9_subset_1(u1_struct_0('#skF_1'),B_33,'#skF_2') = k3_xboole_0(B_33,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_107,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_44])).

tff(c_45,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_14])).

tff(c_131,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_45])).

tff(c_16,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ! [B_35] : k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_3') = k3_xboole_0(B_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [B_35] :
      ( m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_58,plain,(
    ! [B_35] : m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [C_49,A_50,B_51] :
      ( v2_tex_2(C_49,A_50)
      | ~ v2_tex_2(B_51,A_50)
      | ~ r1_tarski(C_49,B_51)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_937,plain,(
    ! [A_90,B_91,A_92] :
      ( v2_tex_2(k3_xboole_0(A_90,B_91),A_92)
      | ~ v2_tex_2(A_90,A_92)
      | ~ m1_subset_1(k3_xboole_0(A_90,B_91),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(A_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_982,plain,(
    ! [B_35] :
      ( v2_tex_2(k3_xboole_0(B_35,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_35,'#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_937])).

tff(c_1380,plain,(
    ! [B_109] :
      ( v2_tex_2(k3_xboole_0(B_109,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_109,'#skF_1')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_982])).

tff(c_1414,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1380])).

tff(c_1429,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_107,c_1414])).

tff(c_1431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1429])).

tff(c_1432,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1473,plain,(
    ! [B_120] : k9_subset_1(u1_struct_0('#skF_1'),B_120,'#skF_2') = k3_xboole_0(B_120,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1443])).

tff(c_1479,plain,(
    ! [B_120] :
      ( m1_subset_1(k3_xboole_0(B_120,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_6])).

tff(c_1485,plain,(
    ! [B_120] : m1_subset_1(k3_xboole_0(B_120,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1479])).

tff(c_1551,plain,(
    ! [C_126,A_127,B_128] :
      ( v2_tex_2(C_126,A_127)
      | ~ v2_tex_2(B_128,A_127)
      | ~ r1_tarski(C_126,B_128)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2035,plain,(
    ! [A_157,B_158,A_159] :
      ( v2_tex_2(k3_xboole_0(A_157,B_158),A_159)
      | ~ v2_tex_2(A_157,A_159)
      | ~ m1_subset_1(k3_xboole_0(A_157,B_158),k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_subset_1(A_157,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_2,c_1551])).

tff(c_2059,plain,(
    ! [B_120] :
      ( v2_tex_2(k3_xboole_0(B_120,'#skF_2'),'#skF_1')
      | ~ v2_tex_2(B_120,'#skF_1')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1485,c_2035])).

tff(c_2427,plain,(
    ! [B_178] :
      ( v2_tex_2(k3_xboole_0(B_178,'#skF_2'),'#skF_1')
      | ~ v2_tex_2(B_178,'#skF_1')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2059])).

tff(c_2458,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_tex_2('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2427])).

tff(c_2475,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_2458])).

tff(c_2477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1540,c_2475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:06:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.79  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.51/1.79  
% 4.58/1.80  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 4.58/1.80  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.58/1.80  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.58/1.80  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.58/1.80  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.58/1.80  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 4.58/1.80  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.58/1.80  tff(c_1443, plain, (![A_112, B_113, C_114]: (k9_subset_1(A_112, B_113, C_114)=k3_xboole_0(B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.80  tff(c_1448, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_1'), B_113, '#skF_3')=k3_xboole_0(B_113, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1443])).
% 4.58/1.80  tff(c_1491, plain, (![A_122, C_123, B_124]: (k9_subset_1(A_122, C_123, B_124)=k9_subset_1(A_122, B_124, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.80  tff(c_1499, plain, (![B_124]: (k9_subset_1(u1_struct_0('#skF_1'), B_124, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_124))), inference(resolution, [status(thm)], [c_18, c_1491])).
% 4.58/1.80  tff(c_1509, plain, (![B_125]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_125)=k3_xboole_0(B_125, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1499])).
% 4.58/1.80  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.58/1.80  tff(c_1449, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_1'), B_113, '#skF_2')=k3_xboole_0(B_113, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1443])).
% 4.58/1.80  tff(c_1516, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_1449])).
% 4.58/1.80  tff(c_14, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.58/1.80  tff(c_1450, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_14])).
% 4.58/1.80  tff(c_1540, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_1450])).
% 4.58/1.80  tff(c_35, plain, (![A_32, B_33, C_34]: (k9_subset_1(A_32, B_33, C_34)=k3_xboole_0(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.58/1.80  tff(c_43, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_1'), B_33, '#skF_3')=k3_xboole_0(B_33, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_35])).
% 4.58/1.80  tff(c_82, plain, (![A_39, C_40, B_41]: (k9_subset_1(A_39, C_40, B_41)=k9_subset_1(A_39, B_41, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.80  tff(c_90, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_41))), inference(resolution, [status(thm)], [c_18, c_82])).
% 4.58/1.80  tff(c_100, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_42)=k3_xboole_0(B_42, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_90])).
% 4.58/1.80  tff(c_44, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_1'), B_33, '#skF_2')=k3_xboole_0(B_33, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_35])).
% 4.58/1.80  tff(c_107, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_44])).
% 4.58/1.80  tff(c_45, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_14])).
% 4.58/1.80  tff(c_131, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_45])).
% 4.58/1.80  tff(c_16, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.58/1.80  tff(c_24, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 4.58/1.80  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.58/1.80  tff(c_46, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_3')=k3_xboole_0(B_35, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_35])).
% 4.58/1.80  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.58/1.80  tff(c_52, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_6])).
% 4.58/1.80  tff(c_58, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 4.58/1.80  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.58/1.80  tff(c_228, plain, (![C_49, A_50, B_51]: (v2_tex_2(C_49, A_50) | ~v2_tex_2(B_51, A_50) | ~r1_tarski(C_49, B_51) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.58/1.80  tff(c_937, plain, (![A_90, B_91, A_92]: (v2_tex_2(k3_xboole_0(A_90, B_91), A_92) | ~v2_tex_2(A_90, A_92) | ~m1_subset_1(k3_xboole_0(A_90, B_91), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(A_90, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_2, c_228])).
% 4.58/1.80  tff(c_982, plain, (![B_35]: (v2_tex_2(k3_xboole_0(B_35, '#skF_3'), '#skF_1') | ~v2_tex_2(B_35, '#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_937])).
% 4.58/1.80  tff(c_1380, plain, (![B_109]: (v2_tex_2(k3_xboole_0(B_109, '#skF_3'), '#skF_1') | ~v2_tex_2(B_109, '#skF_1') | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_982])).
% 4.58/1.80  tff(c_1414, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_1380])).
% 4.58/1.80  tff(c_1429, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_107, c_1414])).
% 4.58/1.80  tff(c_1431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_1429])).
% 4.58/1.80  tff(c_1432, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 4.58/1.80  tff(c_1473, plain, (![B_120]: (k9_subset_1(u1_struct_0('#skF_1'), B_120, '#skF_2')=k3_xboole_0(B_120, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1443])).
% 4.58/1.80  tff(c_1479, plain, (![B_120]: (m1_subset_1(k3_xboole_0(B_120, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1473, c_6])).
% 4.58/1.80  tff(c_1485, plain, (![B_120]: (m1_subset_1(k3_xboole_0(B_120, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1479])).
% 4.58/1.80  tff(c_1551, plain, (![C_126, A_127, B_128]: (v2_tex_2(C_126, A_127) | ~v2_tex_2(B_128, A_127) | ~r1_tarski(C_126, B_128) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.58/1.80  tff(c_2035, plain, (![A_157, B_158, A_159]: (v2_tex_2(k3_xboole_0(A_157, B_158), A_159) | ~v2_tex_2(A_157, A_159) | ~m1_subset_1(k3_xboole_0(A_157, B_158), k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_subset_1(A_157, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_2, c_1551])).
% 4.58/1.80  tff(c_2059, plain, (![B_120]: (v2_tex_2(k3_xboole_0(B_120, '#skF_2'), '#skF_1') | ~v2_tex_2(B_120, '#skF_1') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1485, c_2035])).
% 4.58/1.80  tff(c_2427, plain, (![B_178]: (v2_tex_2(k3_xboole_0(B_178, '#skF_2'), '#skF_1') | ~v2_tex_2(B_178, '#skF_1') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2059])).
% 4.58/1.80  tff(c_2458, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_2427])).
% 4.58/1.80  tff(c_2475, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_2458])).
% 4.58/1.80  tff(c_2477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1540, c_2475])).
% 4.58/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.80  
% 4.58/1.80  Inference rules
% 4.58/1.80  ----------------------
% 4.58/1.80  #Ref     : 0
% 4.58/1.80  #Sup     : 612
% 4.58/1.80  #Fact    : 0
% 4.58/1.80  #Define  : 0
% 4.58/1.80  #Split   : 1
% 4.58/1.80  #Chain   : 0
% 4.58/1.80  #Close   : 0
% 4.58/1.80  
% 4.58/1.80  Ordering : KBO
% 4.58/1.80  
% 4.58/1.80  Simplification rules
% 4.58/1.80  ----------------------
% 4.58/1.80  #Subsume      : 4
% 4.58/1.80  #Demod        : 379
% 4.58/1.80  #Tautology    : 176
% 4.58/1.80  #SimpNegUnit  : 4
% 4.58/1.80  #BackRed      : 4
% 4.58/1.80  
% 4.58/1.80  #Partial instantiations: 0
% 4.58/1.80  #Strategies tried      : 1
% 4.58/1.80  
% 4.58/1.80  Timing (in seconds)
% 4.58/1.80  ----------------------
% 4.58/1.80  Preprocessing        : 0.29
% 4.58/1.80  Parsing              : 0.15
% 4.58/1.80  CNF conversion       : 0.02
% 4.58/1.80  Main loop            : 0.73
% 4.58/1.80  Inferencing          : 0.23
% 4.58/1.80  Reduction            : 0.29
% 4.58/1.80  Demodulation         : 0.22
% 4.58/1.80  BG Simplification    : 0.05
% 4.58/1.80  Subsumption          : 0.10
% 4.58/1.80  Abstraction          : 0.06
% 4.58/1.80  MUC search           : 0.00
% 4.58/1.80  Cooper               : 0.00
% 4.58/1.80  Total                : 1.05
% 4.58/1.80  Index Insertion      : 0.00
% 4.58/1.80  Index Deletion       : 0.00
% 4.58/1.80  Index Matching       : 0.00
% 4.58/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
