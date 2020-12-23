%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 335 expanded)
%              Number of equality atoms :    5 (   7 expanded)
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

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_104,plain,(
    ! [A_52,B_53,C_54] :
      ( k9_subset_1(A_52,B_53,C_54) = k3_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [B_53] : k9_subset_1(u1_struct_0('#skF_1'),B_53,'#skF_3') = k3_xboole_0(B_53,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_123,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_22])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_155,plain,(
    ! [B_60,A_61] :
      ( v4_pre_topc(B_60,A_61)
      | ~ v2_compts_1(B_60,A_61)
      | ~ v8_pre_topc(A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

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
    inference(cnfTransformation,[status(thm)],[f_107])).

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

tff(c_182,plain,(
    ! [B_65,C_66,A_67] :
      ( v4_pre_topc(k3_xboole_0(B_65,C_66),A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v4_pre_topc(C_66,A_67)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v4_pre_topc(B_65,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [B_65] :
      ( v4_pre_topc(k3_xboole_0(B_65,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_65,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_182])).

tff(c_296,plain,(
    ! [B_78] :
      ( v4_pre_topc(k3_xboole_0(B_78,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_78,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_172,c_189])).

tff(c_303,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_296])).

tff(c_310,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_303])).

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

tff(c_276,plain,(
    ! [C_74,A_75,B_76] :
      ( v2_compts_1(C_74,A_75)
      | ~ v4_pre_topc(C_74,A_75)
      | ~ r1_tarski(C_74,B_76)
      | ~ v2_compts_1(B_76,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_736,plain,(
    ! [A_115,B_116,A_117] :
      ( v2_compts_1(k4_xboole_0(A_115,B_116),A_117)
      | ~ v4_pre_topc(k4_xboole_0(A_115,B_116),A_117)
      | ~ v2_compts_1(A_115,A_117)
      | ~ m1_subset_1(k4_xboole_0(A_115,B_116),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(A_115,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_4,c_276])).

tff(c_1094,plain,(
    ! [A_133,B_134,A_135] :
      ( v2_compts_1(k4_xboole_0(A_133,B_134),A_135)
      | ~ v4_pre_topc(k4_xboole_0(A_133,B_134),A_135)
      | ~ v2_compts_1(A_133,A_135)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | ~ r1_tarski(k4_xboole_0(A_133,B_134),u1_struct_0(A_135)) ) ),
    inference(resolution,[status(thm)],[c_14,c_736])).

tff(c_1145,plain,(
    ! [A_136,C_137,A_138] :
      ( v2_compts_1(k4_xboole_0(A_136,C_137),A_138)
      | ~ v4_pre_topc(k4_xboole_0(A_136,C_137),A_138)
      | ~ v2_compts_1(A_136,A_138)
      | ~ m1_subset_1(A_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | ~ r1_tarski(A_136,u1_struct_0(A_138)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1094])).

tff(c_1169,plain,(
    ! [A_6,B_7,A_138] :
      ( v2_compts_1(k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)),A_138)
      | ~ v4_pre_topc(k3_xboole_0(A_6,B_7),A_138)
      | ~ v2_compts_1(A_6,A_138)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | ~ r1_tarski(A_6,u1_struct_0(A_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1145])).

tff(c_1230,plain,(
    ! [A_141,B_142,A_143] :
      ( v2_compts_1(k3_xboole_0(A_141,B_142),A_143)
      | ~ v4_pre_topc(k3_xboole_0(A_141,B_142),A_143)
      | ~ v2_compts_1(A_141,A_143)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | ~ r1_tarski(A_141,u1_struct_0(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1169])).

tff(c_1246,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_310,c_1230])).

tff(c_1270,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_36,c_34,c_32,c_26,c_1246])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.68  
% 3.79/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.68  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.79/1.68  
% 3.79/1.68  %Foreground sorts:
% 3.79/1.68  
% 3.79/1.68  
% 3.79/1.68  %Background operators:
% 3.79/1.68  
% 3.79/1.68  
% 3.79/1.68  %Foreground operators:
% 3.79/1.68  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.79/1.68  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.79/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.79/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.79/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.79/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.79/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.79/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.79/1.68  
% 3.79/1.69  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.79/1.69  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.79/1.69  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.79/1.69  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.79/1.69  tff(f_57, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tops_1)).
% 3.79/1.69  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.79/1.69  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.79/1.69  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.79/1.69  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.79/1.69  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_104, plain, (![A_52, B_53, C_54]: (k9_subset_1(A_52, B_53, C_54)=k3_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.79/1.69  tff(c_113, plain, (![B_53]: (k9_subset_1(u1_struct_0('#skF_1'), B_53, '#skF_3')=k3_xboole_0(B_53, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_104])).
% 3.79/1.69  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_123, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_22])).
% 3.79/1.69  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_38, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.69  tff(c_45, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 3.79/1.69  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_155, plain, (![B_60, A_61]: (v4_pre_topc(B_60, A_61) | ~v2_compts_1(B_60, A_61) | ~v8_pre_topc(A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.79/1.69  tff(c_162, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_155])).
% 3.79/1.69  tff(c_169, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_162])).
% 3.79/1.69  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.79/1.69  tff(c_165, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_155])).
% 3.79/1.69  tff(c_172, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_165])).
% 3.79/1.69  tff(c_182, plain, (![B_65, C_66, A_67]: (v4_pre_topc(k3_xboole_0(B_65, C_66), A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~v4_pre_topc(C_66, A_67) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_67))) | ~v4_pre_topc(B_65, A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.79/1.69  tff(c_189, plain, (![B_65]: (v4_pre_topc(k3_xboole_0(B_65, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_65, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_182])).
% 3.79/1.69  tff(c_296, plain, (![B_78]: (v4_pre_topc(k3_xboole_0(B_78, '#skF_3'), '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_78, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_172, c_189])).
% 3.79/1.69  tff(c_303, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_296])).
% 3.79/1.69  tff(c_310, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_303])).
% 3.79/1.69  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.79/1.69  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.69  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.69  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.69  tff(c_276, plain, (![C_74, A_75, B_76]: (v2_compts_1(C_74, A_75) | ~v4_pre_topc(C_74, A_75) | ~r1_tarski(C_74, B_76) | ~v2_compts_1(B_76, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.79/1.69  tff(c_736, plain, (![A_115, B_116, A_117]: (v2_compts_1(k4_xboole_0(A_115, B_116), A_117) | ~v4_pre_topc(k4_xboole_0(A_115, B_116), A_117) | ~v2_compts_1(A_115, A_117) | ~m1_subset_1(k4_xboole_0(A_115, B_116), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(A_115, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117))), inference(resolution, [status(thm)], [c_4, c_276])).
% 3.79/1.69  tff(c_1094, plain, (![A_133, B_134, A_135]: (v2_compts_1(k4_xboole_0(A_133, B_134), A_135) | ~v4_pre_topc(k4_xboole_0(A_133, B_134), A_135) | ~v2_compts_1(A_133, A_135) | ~m1_subset_1(A_133, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | ~r1_tarski(k4_xboole_0(A_133, B_134), u1_struct_0(A_135)))), inference(resolution, [status(thm)], [c_14, c_736])).
% 3.79/1.69  tff(c_1145, plain, (![A_136, C_137, A_138]: (v2_compts_1(k4_xboole_0(A_136, C_137), A_138) | ~v4_pre_topc(k4_xboole_0(A_136, C_137), A_138) | ~v2_compts_1(A_136, A_138) | ~m1_subset_1(A_136, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | ~r1_tarski(A_136, u1_struct_0(A_138)))), inference(resolution, [status(thm)], [c_2, c_1094])).
% 3.79/1.69  tff(c_1169, plain, (![A_6, B_7, A_138]: (v2_compts_1(k4_xboole_0(A_6, k4_xboole_0(A_6, B_7)), A_138) | ~v4_pre_topc(k3_xboole_0(A_6, B_7), A_138) | ~v2_compts_1(A_6, A_138) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | ~r1_tarski(A_6, u1_struct_0(A_138)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1145])).
% 3.79/1.69  tff(c_1230, plain, (![A_141, B_142, A_143]: (v2_compts_1(k3_xboole_0(A_141, B_142), A_143) | ~v4_pre_topc(k3_xboole_0(A_141, B_142), A_143) | ~v2_compts_1(A_141, A_143) | ~m1_subset_1(A_141, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | ~r1_tarski(A_141, u1_struct_0(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1169])).
% 3.79/1.69  tff(c_1246, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_310, c_1230])).
% 3.79/1.69  tff(c_1270, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_36, c_34, c_32, c_26, c_1246])).
% 3.79/1.69  tff(c_1272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1270])).
% 3.79/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.69  
% 3.79/1.69  Inference rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Ref     : 0
% 3.79/1.69  #Sup     : 303
% 3.79/1.69  #Fact    : 0
% 3.79/1.69  #Define  : 0
% 3.79/1.69  #Split   : 0
% 3.79/1.69  #Chain   : 0
% 3.79/1.69  #Close   : 0
% 3.79/1.69  
% 3.79/1.69  Ordering : KBO
% 3.79/1.69  
% 3.79/1.69  Simplification rules
% 3.79/1.69  ----------------------
% 3.79/1.69  #Subsume      : 34
% 3.79/1.69  #Demod        : 533
% 3.79/1.69  #Tautology    : 123
% 3.79/1.69  #SimpNegUnit  : 1
% 3.79/1.69  #BackRed      : 1
% 3.79/1.69  
% 3.79/1.69  #Partial instantiations: 0
% 3.79/1.69  #Strategies tried      : 1
% 3.79/1.69  
% 3.79/1.69  Timing (in seconds)
% 3.79/1.69  ----------------------
% 3.79/1.70  Preprocessing        : 0.32
% 3.79/1.70  Parsing              : 0.18
% 3.79/1.70  CNF conversion       : 0.02
% 3.79/1.70  Main loop            : 0.52
% 3.79/1.70  Inferencing          : 0.19
% 3.79/1.70  Reduction            : 0.20
% 3.79/1.70  Demodulation         : 0.16
% 3.79/1.70  BG Simplification    : 0.02
% 3.79/1.70  Subsumption          : 0.08
% 3.79/1.70  Abstraction          : 0.03
% 3.79/1.70  MUC search           : 0.00
% 3.79/1.70  Cooper               : 0.00
% 3.79/1.70  Total                : 0.87
% 3.79/1.70  Index Insertion      : 0.00
% 3.79/1.70  Index Deletion       : 0.00
% 3.79/1.70  Index Matching       : 0.00
% 3.79/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
