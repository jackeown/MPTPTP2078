%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 313 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k8_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_105,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k8_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_86,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_115,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_176,plain,(
    ! [B_60,A_61] :
      ( v4_pre_topc(B_60,A_61)
      | ~ v2_compts_1(B_60,A_61)
      | ~ v8_pre_topc(A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_195,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_214,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_195])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_198,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_217,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_198])).

tff(c_258,plain,(
    ! [B_76,C_77,A_78] :
      ( v4_pre_topc(k3_xboole_0(B_76,C_77),A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v4_pre_topc(C_77,A_78)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v4_pre_topc(B_76,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    ! [B_76] :
      ( v4_pre_topc(k3_xboole_0(B_76,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_76,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_258])).

tff(c_336,plain,(
    ! [B_80] :
      ( v4_pre_topc(k3_xboole_0(B_80,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_80,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_217,c_275])).

tff(c_358,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_336])).

tff(c_370,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_358])).

tff(c_43,plain,(
    ! [A_35,B_36,C_37] :
      ( k8_subset_1(A_35,B_36,C_37) = k3_xboole_0(B_36,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [C_37] : k8_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_37) = k3_xboole_0('#skF_2',C_37) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_84,plain,(
    ! [A_44,B_45,C_46] :
      ( m1_subset_1(k8_subset_1(A_44,B_45,C_46),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [C_37] :
      ( m1_subset_1(k3_xboole_0('#skF_2',C_37),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_100,plain,(
    ! [C_37] : m1_subset_1(k3_xboole_0('#skF_2',C_37),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_94])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_377,plain,(
    ! [C_84,A_85,B_86] :
      ( v2_compts_1(C_84,A_85)
      | ~ v4_pre_topc(C_84,A_85)
      | ~ r1_tarski(C_84,B_86)
      | ~ v2_compts_1(B_86,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_674,plain,(
    ! [A_165,B_166,A_167] :
      ( v2_compts_1(k3_xboole_0(A_165,B_166),A_167)
      | ~ v4_pre_topc(k3_xboole_0(A_165,B_166),A_167)
      | ~ v2_compts_1(A_165,A_167)
      | ~ m1_subset_1(k3_xboole_0(A_165,B_166),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(A_165,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_2,c_377])).

tff(c_695,plain,(
    ! [C_37] :
      ( v2_compts_1(k3_xboole_0('#skF_2',C_37),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',C_37),'#skF_1')
      | ~ v2_compts_1('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_100,c_674])).

tff(c_723,plain,(
    ! [C_168] :
      ( v2_compts_1(k3_xboole_0('#skF_2',C_168),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',C_168),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_22,c_695])).

tff(c_734,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_370,c_723])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.45  
% 3.11/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.45  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k8_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.11/1.45  
% 3.11/1.45  %Foreground sorts:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Background operators:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Foreground operators:
% 3.11/1.45  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.11/1.45  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.45  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 3.11/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.11/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.11/1.45  
% 3.13/1.47  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 3.13/1.47  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.13/1.47  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 3.13/1.47  tff(f_55, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 3.13/1.47  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 3.13/1.47  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k8_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 3.13/1.47  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.13/1.47  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 3.13/1.47  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_68, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.47  tff(c_74, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_68])).
% 3.13/1.47  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_115, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 3.13/1.47  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_176, plain, (![B_60, A_61]: (v4_pre_topc(B_60, A_61) | ~v2_compts_1(B_60, A_61) | ~v8_pre_topc(A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.47  tff(c_195, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_176])).
% 3.13/1.47  tff(c_214, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_195])).
% 3.13/1.47  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.13/1.47  tff(c_198, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_176])).
% 3.13/1.47  tff(c_217, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_198])).
% 3.13/1.47  tff(c_258, plain, (![B_76, C_77, A_78]: (v4_pre_topc(k3_xboole_0(B_76, C_77), A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v4_pre_topc(C_77, A_78) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_78))) | ~v4_pre_topc(B_76, A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.47  tff(c_275, plain, (![B_76]: (v4_pre_topc(k3_xboole_0(B_76, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_76, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_258])).
% 3.13/1.47  tff(c_336, plain, (![B_80]: (v4_pre_topc(k3_xboole_0(B_80, '#skF_3'), '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_80, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_217, c_275])).
% 3.13/1.47  tff(c_358, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_336])).
% 3.13/1.47  tff(c_370, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_358])).
% 3.13/1.47  tff(c_43, plain, (![A_35, B_36, C_37]: (k8_subset_1(A_35, B_36, C_37)=k3_xboole_0(B_36, C_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.47  tff(c_48, plain, (![C_37]: (k8_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_37)=k3_xboole_0('#skF_2', C_37))), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.13/1.47  tff(c_84, plain, (![A_44, B_45, C_46]: (m1_subset_1(k8_subset_1(A_44, B_45, C_46), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.47  tff(c_94, plain, (![C_37]: (m1_subset_1(k3_xboole_0('#skF_2', C_37), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_84])).
% 3.13/1.47  tff(c_100, plain, (![C_37]: (m1_subset_1(k3_xboole_0('#skF_2', C_37), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_94])).
% 3.13/1.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.47  tff(c_377, plain, (![C_84, A_85, B_86]: (v2_compts_1(C_84, A_85) | ~v4_pre_topc(C_84, A_85) | ~r1_tarski(C_84, B_86) | ~v2_compts_1(B_86, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.13/1.47  tff(c_674, plain, (![A_165, B_166, A_167]: (v2_compts_1(k3_xboole_0(A_165, B_166), A_167) | ~v4_pre_topc(k3_xboole_0(A_165, B_166), A_167) | ~v2_compts_1(A_165, A_167) | ~m1_subset_1(k3_xboole_0(A_165, B_166), k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(A_165, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167))), inference(resolution, [status(thm)], [c_2, c_377])).
% 3.13/1.47  tff(c_695, plain, (![C_37]: (v2_compts_1(k3_xboole_0('#skF_2', C_37), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', C_37), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_100, c_674])).
% 3.13/1.47  tff(c_723, plain, (![C_168]: (v2_compts_1(k3_xboole_0('#skF_2', C_168), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', C_168), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_22, c_695])).
% 3.13/1.47  tff(c_734, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_370, c_723])).
% 3.13/1.47  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_734])).
% 3.13/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  Inference rules
% 3.13/1.47  ----------------------
% 3.13/1.47  #Ref     : 0
% 3.13/1.47  #Sup     : 152
% 3.13/1.47  #Fact    : 0
% 3.13/1.47  #Define  : 0
% 3.13/1.47  #Split   : 0
% 3.13/1.47  #Chain   : 0
% 3.13/1.47  #Close   : 0
% 3.13/1.47  
% 3.13/1.47  Ordering : KBO
% 3.13/1.47  
% 3.13/1.47  Simplification rules
% 3.13/1.47  ----------------------
% 3.13/1.47  #Subsume      : 6
% 3.13/1.47  #Demod        : 172
% 3.13/1.47  #Tautology    : 45
% 3.13/1.47  #SimpNegUnit  : 1
% 3.13/1.47  #BackRed      : 1
% 3.13/1.47  
% 3.13/1.47  #Partial instantiations: 0
% 3.13/1.47  #Strategies tried      : 1
% 3.13/1.47  
% 3.13/1.47  Timing (in seconds)
% 3.13/1.47  ----------------------
% 3.13/1.47  Preprocessing        : 0.32
% 3.13/1.47  Parsing              : 0.17
% 3.13/1.47  CNF conversion       : 0.02
% 3.13/1.47  Main loop            : 0.40
% 3.13/1.47  Inferencing          : 0.16
% 3.13/1.47  Reduction            : 0.13
% 3.13/1.47  Demodulation         : 0.10
% 3.13/1.47  BG Simplification    : 0.02
% 3.13/1.47  Subsumption          : 0.06
% 3.13/1.47  Abstraction          : 0.03
% 3.13/1.47  MUC search           : 0.00
% 3.13/1.47  Cooper               : 0.00
% 3.13/1.47  Total                : 0.75
% 3.13/1.47  Index Insertion      : 0.00
% 3.13/1.47  Index Deletion       : 0.00
% 3.13/1.47  Index Matching       : 0.00
% 3.13/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
