%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 10.05s
% Output     : CNFRefutation 10.05s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 190 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 ( 387 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_38,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_23] :
      ( v1_xboole_0(k1_struct_0(A_23))
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_104,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_114,plain,(
    ! [A_52,A_53] :
      ( ~ v1_xboole_0(A_52)
      | ~ r2_hidden(A_53,A_52) ) ),
    inference(resolution,[status(thm)],[c_41,c_104])).

tff(c_118,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_24] :
      ( k3_subset_1(u1_struct_0(A_24),k1_struct_0(A_24)) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_229,plain,(
    ! [C_85,A_86,B_87] :
      ( r1_tarski(C_85,k3_subset_1(A_86,B_87))
      | ~ r1_tarski(B_87,k3_subset_1(A_86,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_792,plain,(
    ! [C_164,A_165,A_166] :
      ( r1_tarski(C_164,k3_subset_1(A_165,A_166))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_165))
      | ~ m1_subset_1(A_166,k1_zfmisc_1(A_165))
      | ~ v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_118,c_229])).

tff(c_9472,plain,(
    ! [C_2907,A_2908] :
      ( r1_tarski(C_2907,k2_struct_0(A_2908))
      | ~ m1_subset_1(C_2907,k1_zfmisc_1(u1_struct_0(A_2908)))
      | ~ m1_subset_1(k1_struct_0(A_2908),k1_zfmisc_1(u1_struct_0(A_2908)))
      | ~ v1_xboole_0(k1_struct_0(A_2908))
      | ~ l1_struct_0(A_2908) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_792])).

tff(c_9505,plain,(
    ! [A_2933] :
      ( r1_tarski(u1_struct_0(A_2933),k2_struct_0(A_2933))
      | ~ m1_subset_1(k1_struct_0(A_2933),k1_zfmisc_1(u1_struct_0(A_2933)))
      | ~ v1_xboole_0(k1_struct_0(A_2933))
      | ~ l1_struct_0(A_2933) ) ),
    inference(resolution,[status(thm)],[c_41,c_9472])).

tff(c_9519,plain,(
    ! [A_2945] :
      ( r1_tarski(u1_struct_0(A_2945),k2_struct_0(A_2945))
      | ~ v1_xboole_0(k1_struct_0(A_2945))
      | ~ l1_struct_0(A_2945)
      | ~ r1_tarski(k1_struct_0(A_2945),u1_struct_0(A_2945)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9505])).

tff(c_74,plain,(
    ! [A_39] :
      ( m1_subset_1(k2_struct_0(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_39] :
      ( r1_tarski(k2_struct_0(A_39),u1_struct_0(A_39))
      | ~ l1_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_74,c_20])).

tff(c_100,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_270,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),B_95)
      | ~ r1_tarski(A_93,B_95)
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_383,plain,(
    ! [A_115,B_116,B_117,B_118] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(B_118,B_117)
      | ~ r1_tarski(A_115,B_118)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_820,plain,(
    ! [A_167,B_168,A_169] :
      ( r2_hidden('#skF_1'(A_167,B_168),u1_struct_0(A_169))
      | ~ r1_tarski(A_167,k2_struct_0(A_169))
      | r1_tarski(A_167,B_168)
      | ~ l1_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_78,c_383])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_836,plain,(
    ! [A_170,A_171] :
      ( ~ r1_tarski(A_170,k2_struct_0(A_171))
      | r1_tarski(A_170,u1_struct_0(A_171))
      | ~ l1_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_820,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_868,plain,(
    ! [A_171,A_170] :
      ( u1_struct_0(A_171) = A_170
      | ~ r1_tarski(u1_struct_0(A_171),A_170)
      | ~ r1_tarski(A_170,k2_struct_0(A_171))
      | ~ l1_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_836,c_8])).

tff(c_9573,plain,(
    ! [A_2945] :
      ( u1_struct_0(A_2945) = k2_struct_0(A_2945)
      | ~ r1_tarski(k2_struct_0(A_2945),k2_struct_0(A_2945))
      | ~ v1_xboole_0(k1_struct_0(A_2945))
      | ~ l1_struct_0(A_2945)
      | ~ r1_tarski(k1_struct_0(A_2945),u1_struct_0(A_2945)) ) ),
    inference(resolution,[status(thm)],[c_9519,c_868])).

tff(c_9644,plain,(
    ! [A_2957] :
      ( u1_struct_0(A_2957) = k2_struct_0(A_2957)
      | ~ v1_xboole_0(k1_struct_0(A_2957))
      | ~ l1_struct_0(A_2957)
      | ~ r1_tarski(k1_struct_0(A_2957),u1_struct_0(A_2957)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9573])).

tff(c_9660,plain,(
    ! [A_2969] :
      ( u1_struct_0(A_2969) = k2_struct_0(A_2969)
      | ~ l1_struct_0(A_2969)
      | ~ v1_xboole_0(k1_struct_0(A_2969)) ) ),
    inference(resolution,[status(thm)],[c_118,c_9644])).

tff(c_9753,plain,(
    ! [A_2996] :
      ( u1_struct_0(A_2996) = k2_struct_0(A_2996)
      | ~ l1_struct_0(A_2996) ) ),
    inference(resolution,[status(thm)],[c_32,c_9660])).

tff(c_9758,plain,(
    ! [A_3008] :
      ( u1_struct_0(A_3008) = k2_struct_0(A_3008)
      | ~ l1_pre_topc(A_3008) ) ),
    inference(resolution,[status(thm)],[c_30,c_9753])).

tff(c_9762,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_9758])).

tff(c_171,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k2_pre_topc(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_pre_topc(A_70,B_71),u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_171,c_20])).

tff(c_123,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,k2_pre_topc(A_57,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_200,plain,(
    ! [A_79] :
      ( r1_tarski(u1_struct_0(A_79),k2_pre_topc(A_79,u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_41,c_123])).

tff(c_445,plain,(
    ! [A_132] :
      ( k2_pre_topc(A_132,u1_struct_0(A_132)) = u1_struct_0(A_132)
      | ~ r1_tarski(k2_pre_topc(A_132,u1_struct_0(A_132)),u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_449,plain,(
    ! [A_70] :
      ( k2_pre_topc(A_70,u1_struct_0(A_70)) = u1_struct_0(A_70)
      | ~ m1_subset_1(u1_struct_0(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_181,c_445])).

tff(c_455,plain,(
    ! [A_70] :
      ( k2_pre_topc(A_70,u1_struct_0(A_70)) = u1_struct_0(A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_449])).

tff(c_9994,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9762,c_455])).

tff(c_10179,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9762,c_9994])).

tff(c_10181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_10179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.05/3.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.45  
% 10.05/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_2 > #skF_1
% 10.05/3.45  
% 10.05/3.45  %Foreground sorts:
% 10.05/3.45  
% 10.05/3.45  
% 10.05/3.45  %Background operators:
% 10.05/3.45  
% 10.05/3.45  
% 10.05/3.45  %Foreground operators:
% 10.05/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.05/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.05/3.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.05/3.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.05/3.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.05/3.45  tff('#skF_2', type, '#skF_2': $i).
% 10.05/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.05/3.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.05/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.05/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.05/3.45  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 10.05/3.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.05/3.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.05/3.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.05/3.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.05/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.05/3.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.05/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.05/3.45  
% 10.05/3.47  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 10.05/3.47  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.05/3.47  tff(f_80, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 10.05/3.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.05/3.47  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.05/3.47  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.05/3.47  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 10.05/3.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.05/3.47  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.05/3.47  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 10.05/3.47  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 10.05/3.47  tff(f_72, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 10.05/3.47  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.05/3.47  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.05/3.47  tff(c_38, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.05/3.47  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.05/3.47  tff(c_30, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.05/3.47  tff(c_32, plain, (![A_23]: (v1_xboole_0(k1_struct_0(A_23)) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.05/3.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.05/3.47  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.05/3.47  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.05/3.47  tff(c_41, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 10.05/3.47  tff(c_104, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.05/3.47  tff(c_114, plain, (![A_52, A_53]: (~v1_xboole_0(A_52) | ~r2_hidden(A_53, A_52))), inference(resolution, [status(thm)], [c_41, c_104])).
% 10.05/3.47  tff(c_118, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_114])).
% 10.05/3.47  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.05/3.47  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.05/3.47  tff(c_34, plain, (![A_24]: (k3_subset_1(u1_struct_0(A_24), k1_struct_0(A_24))=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.05/3.47  tff(c_229, plain, (![C_85, A_86, B_87]: (r1_tarski(C_85, k3_subset_1(A_86, B_87)) | ~r1_tarski(B_87, k3_subset_1(A_86, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.05/3.47  tff(c_792, plain, (![C_164, A_165, A_166]: (r1_tarski(C_164, k3_subset_1(A_165, A_166)) | ~m1_subset_1(C_164, k1_zfmisc_1(A_165)) | ~m1_subset_1(A_166, k1_zfmisc_1(A_165)) | ~v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_118, c_229])).
% 10.05/3.47  tff(c_9472, plain, (![C_2907, A_2908]: (r1_tarski(C_2907, k2_struct_0(A_2908)) | ~m1_subset_1(C_2907, k1_zfmisc_1(u1_struct_0(A_2908))) | ~m1_subset_1(k1_struct_0(A_2908), k1_zfmisc_1(u1_struct_0(A_2908))) | ~v1_xboole_0(k1_struct_0(A_2908)) | ~l1_struct_0(A_2908))), inference(superposition, [status(thm), theory('equality')], [c_34, c_792])).
% 10.05/3.47  tff(c_9505, plain, (![A_2933]: (r1_tarski(u1_struct_0(A_2933), k2_struct_0(A_2933)) | ~m1_subset_1(k1_struct_0(A_2933), k1_zfmisc_1(u1_struct_0(A_2933))) | ~v1_xboole_0(k1_struct_0(A_2933)) | ~l1_struct_0(A_2933))), inference(resolution, [status(thm)], [c_41, c_9472])).
% 10.05/3.47  tff(c_9519, plain, (![A_2945]: (r1_tarski(u1_struct_0(A_2945), k2_struct_0(A_2945)) | ~v1_xboole_0(k1_struct_0(A_2945)) | ~l1_struct_0(A_2945) | ~r1_tarski(k1_struct_0(A_2945), u1_struct_0(A_2945)))), inference(resolution, [status(thm)], [c_22, c_9505])).
% 10.05/3.47  tff(c_74, plain, (![A_39]: (m1_subset_1(k2_struct_0(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.05/3.47  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.05/3.47  tff(c_78, plain, (![A_39]: (r1_tarski(k2_struct_0(A_39), u1_struct_0(A_39)) | ~l1_struct_0(A_39))), inference(resolution, [status(thm)], [c_74, c_20])).
% 10.05/3.47  tff(c_100, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.05/3.47  tff(c_270, plain, (![A_93, B_94, B_95]: (r2_hidden('#skF_1'(A_93, B_94), B_95) | ~r1_tarski(A_93, B_95) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_100])).
% 10.05/3.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.05/3.47  tff(c_383, plain, (![A_115, B_116, B_117, B_118]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(B_118, B_117) | ~r1_tarski(A_115, B_118) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_270, c_2])).
% 10.05/3.47  tff(c_820, plain, (![A_167, B_168, A_169]: (r2_hidden('#skF_1'(A_167, B_168), u1_struct_0(A_169)) | ~r1_tarski(A_167, k2_struct_0(A_169)) | r1_tarski(A_167, B_168) | ~l1_struct_0(A_169))), inference(resolution, [status(thm)], [c_78, c_383])).
% 10.05/3.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.05/3.47  tff(c_836, plain, (![A_170, A_171]: (~r1_tarski(A_170, k2_struct_0(A_171)) | r1_tarski(A_170, u1_struct_0(A_171)) | ~l1_struct_0(A_171))), inference(resolution, [status(thm)], [c_820, c_4])).
% 10.05/3.47  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.05/3.47  tff(c_868, plain, (![A_171, A_170]: (u1_struct_0(A_171)=A_170 | ~r1_tarski(u1_struct_0(A_171), A_170) | ~r1_tarski(A_170, k2_struct_0(A_171)) | ~l1_struct_0(A_171))), inference(resolution, [status(thm)], [c_836, c_8])).
% 10.05/3.47  tff(c_9573, plain, (![A_2945]: (u1_struct_0(A_2945)=k2_struct_0(A_2945) | ~r1_tarski(k2_struct_0(A_2945), k2_struct_0(A_2945)) | ~v1_xboole_0(k1_struct_0(A_2945)) | ~l1_struct_0(A_2945) | ~r1_tarski(k1_struct_0(A_2945), u1_struct_0(A_2945)))), inference(resolution, [status(thm)], [c_9519, c_868])).
% 10.05/3.47  tff(c_9644, plain, (![A_2957]: (u1_struct_0(A_2957)=k2_struct_0(A_2957) | ~v1_xboole_0(k1_struct_0(A_2957)) | ~l1_struct_0(A_2957) | ~r1_tarski(k1_struct_0(A_2957), u1_struct_0(A_2957)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9573])).
% 10.05/3.47  tff(c_9660, plain, (![A_2969]: (u1_struct_0(A_2969)=k2_struct_0(A_2969) | ~l1_struct_0(A_2969) | ~v1_xboole_0(k1_struct_0(A_2969)))), inference(resolution, [status(thm)], [c_118, c_9644])).
% 10.05/3.47  tff(c_9753, plain, (![A_2996]: (u1_struct_0(A_2996)=k2_struct_0(A_2996) | ~l1_struct_0(A_2996))), inference(resolution, [status(thm)], [c_32, c_9660])).
% 10.05/3.47  tff(c_9758, plain, (![A_3008]: (u1_struct_0(A_3008)=k2_struct_0(A_3008) | ~l1_pre_topc(A_3008))), inference(resolution, [status(thm)], [c_30, c_9753])).
% 10.05/3.47  tff(c_9762, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_9758])).
% 10.05/3.47  tff(c_171, plain, (![A_70, B_71]: (m1_subset_1(k2_pre_topc(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.05/3.47  tff(c_181, plain, (![A_70, B_71]: (r1_tarski(k2_pre_topc(A_70, B_71), u1_struct_0(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_171, c_20])).
% 10.05/3.47  tff(c_123, plain, (![B_56, A_57]: (r1_tarski(B_56, k2_pre_topc(A_57, B_56)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.05/3.47  tff(c_200, plain, (![A_79]: (r1_tarski(u1_struct_0(A_79), k2_pre_topc(A_79, u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_41, c_123])).
% 10.05/3.47  tff(c_445, plain, (![A_132]: (k2_pre_topc(A_132, u1_struct_0(A_132))=u1_struct_0(A_132) | ~r1_tarski(k2_pre_topc(A_132, u1_struct_0(A_132)), u1_struct_0(A_132)) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_200, c_8])).
% 10.05/3.47  tff(c_449, plain, (![A_70]: (k2_pre_topc(A_70, u1_struct_0(A_70))=u1_struct_0(A_70) | ~m1_subset_1(u1_struct_0(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_181, c_445])).
% 10.05/3.47  tff(c_455, plain, (![A_70]: (k2_pre_topc(A_70, u1_struct_0(A_70))=u1_struct_0(A_70) | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_449])).
% 10.05/3.47  tff(c_9994, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9762, c_455])).
% 10.05/3.47  tff(c_10179, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9762, c_9994])).
% 10.05/3.47  tff(c_10181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_10179])).
% 10.05/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.47  
% 10.05/3.47  Inference rules
% 10.05/3.47  ----------------------
% 10.05/3.47  #Ref     : 0
% 10.05/3.47  #Sup     : 2448
% 10.05/3.47  #Fact    : 0
% 10.05/3.47  #Define  : 0
% 10.05/3.47  #Split   : 7
% 10.05/3.47  #Chain   : 0
% 10.05/3.47  #Close   : 0
% 10.05/3.47  
% 10.05/3.47  Ordering : KBO
% 10.05/3.47  
% 10.05/3.47  Simplification rules
% 10.05/3.47  ----------------------
% 10.05/3.47  #Subsume      : 1620
% 10.05/3.47  #Demod        : 472
% 10.05/3.47  #Tautology    : 89
% 10.05/3.47  #SimpNegUnit  : 13
% 10.05/3.47  #BackRed      : 12
% 10.05/3.47  
% 10.05/3.47  #Partial instantiations: 1908
% 10.05/3.47  #Strategies tried      : 1
% 10.05/3.47  
% 10.05/3.47  Timing (in seconds)
% 10.05/3.47  ----------------------
% 10.05/3.47  Preprocessing        : 0.29
% 10.05/3.47  Parsing              : 0.16
% 10.05/3.47  CNF conversion       : 0.02
% 10.05/3.47  Main loop            : 2.38
% 10.05/3.47  Inferencing          : 0.60
% 10.05/3.47  Reduction            : 0.41
% 10.05/3.47  Demodulation         : 0.25
% 10.05/3.47  BG Simplification    : 0.06
% 10.05/3.47  Subsumption          : 1.18
% 10.05/3.47  Abstraction          : 0.09
% 10.05/3.47  MUC search           : 0.00
% 10.05/3.47  Cooper               : 0.00
% 10.05/3.47  Total                : 2.70
% 10.05/3.47  Index Insertion      : 0.00
% 10.05/3.47  Index Deletion       : 0.00
% 10.05/3.47  Index Matching       : 0.00
% 10.05/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
