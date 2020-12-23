%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:30 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 198 expanded)
%              Number of leaves         :   52 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 315 expanded)
%              Number of equality atoms :   45 (  98 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_126,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_106,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_141,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_162,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_190,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_197,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_87,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_88,plain,(
    k1_tops_1('#skF_5',k2_struct_0('#skF_5')) != k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_60,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    ! [A_38] : r1_tarski(k1_tarski(A_38),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_359,plain,(
    ! [A_114,B_115] : k4_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = k3_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_407,plain,(
    ! [B_116] : k3_xboole_0(k1_xboole_0,B_116) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_28])).

tff(c_20,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_412,plain,(
    ! [B_116,C_17] :
      ( ~ r1_xboole_0(k1_xboole_0,B_116)
      | ~ r2_hidden(C_17,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_20])).

tff(c_420,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_437,plain,(
    ! [B_9] : r1_xboole_0(k1_xboole_0,B_9) ),
    inference(resolution,[status(thm)],[c_16,c_420])).

tff(c_115,plain,(
    ! [B_75,A_76] : k2_xboole_0(B_75,A_76) = k2_xboole_0(A_76,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [A_76] : k2_xboole_0(k1_xboole_0,A_76) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_22])).

tff(c_535,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(k2_xboole_0(A_138,B_139),B_139) = A_138
      | ~ r1_xboole_0(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_553,plain,(
    ! [A_76] :
      ( k4_xboole_0(A_76,A_76) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_535])).

tff(c_643,plain,(
    ! [A_144] : k4_xboole_0(A_144,A_144) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_553])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | k4_xboole_0(k1_tarski(A_32),B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_757,plain,(
    ! [A_147] : r2_hidden(A_147,k1_tarski(A_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_38])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_949,plain,(
    ! [A_161,B_162] :
      ( r2_hidden(A_161,B_162)
      | ~ r1_tarski(k1_tarski(A_161),B_162) ) ),
    inference(resolution,[status(thm)],[c_757,c_4])).

tff(c_960,plain,(
    ! [A_163] : r2_hidden(A_163,k1_zfmisc_1(A_163)) ),
    inference(resolution,[status(thm)],[c_48,c_949])).

tff(c_50,plain,(
    ! [B_40,A_39] :
      ( m1_subset_1(B_40,A_39)
      | ~ r2_hidden(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_965,plain,(
    ! [A_163] :
      ( m1_subset_1(A_163,k1_zfmisc_1(A_163))
      | v1_xboole_0(k1_zfmisc_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_960,c_50])).

tff(c_969,plain,(
    ! [A_163] : m1_subset_1(A_163,k1_zfmisc_1(A_163)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_965])).

tff(c_30,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_562,plain,(
    ! [A_18] :
      ( k4_xboole_0(A_18,k1_xboole_0) = A_18
      | ~ r1_xboole_0(A_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_535])).

tff(c_568,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_562])).

tff(c_68,plain,(
    ! [A_50] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1147,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = k3_subset_1(A_183,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1175,plain,(
    ! [A_50] : k4_xboole_0(A_50,k1_xboole_0) = k3_subset_1(A_50,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_1147])).

tff(c_1185,plain,(
    ! [A_50] : k3_subset_1(A_50,k1_xboole_0) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_1175])).

tff(c_92,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_90,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1676,plain,(
    ! [B_217,A_218] :
      ( v4_pre_topc(B_217,A_218)
      | ~ v1_xboole_0(B_217)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1710,plain,(
    ! [A_218] :
      ( v4_pre_topc(k1_xboole_0,A_218)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_68,c_1676])).

tff(c_1723,plain,(
    ! [A_219] :
      ( v4_pre_topc(k1_xboole_0,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1710])).

tff(c_76,plain,(
    ! [A_58] :
      ( l1_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_200,plain,(
    ! [A_78] :
      ( u1_struct_0(A_78) = k2_struct_0(A_78)
      | ~ l1_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_207,plain,(
    ! [A_79] :
      ( u1_struct_0(A_79) = k2_struct_0(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_76,c_200])).

tff(c_211,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_207])).

tff(c_1414,plain,(
    ! [A_194,B_195] :
      ( k2_pre_topc(A_194,B_195) = B_195
      | ~ v4_pre_topc(B_195,A_194)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1444,plain,(
    ! [B_195] :
      ( k2_pre_topc('#skF_5',B_195) = B_195
      | ~ v4_pre_topc(B_195,'#skF_5')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_1414])).

tff(c_1461,plain,(
    ! [B_197] :
      ( k2_pre_topc('#skF_5',B_197) = B_197
      | ~ v4_pre_topc(B_197,'#skF_5')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1444])).

tff(c_1500,plain,
    ( k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1461])).

tff(c_1501,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1500])).

tff(c_1726,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1723,c_1501])).

tff(c_1733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1726])).

tff(c_1734,plain,(
    k2_pre_topc('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1500])).

tff(c_873,plain,(
    ! [A_153,B_154] :
      ( k3_subset_1(A_153,k3_subset_1(A_153,B_154)) = B_154
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_886,plain,(
    ! [A_50] : k3_subset_1(A_50,k3_subset_1(A_50,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_873])).

tff(c_1186,plain,(
    ! [A_50] : k3_subset_1(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_886])).

tff(c_2700,plain,(
    ! [A_299,B_300] :
      ( k3_subset_1(u1_struct_0(A_299),k2_pre_topc(A_299,k3_subset_1(u1_struct_0(A_299),B_300))) = k1_tops_1(A_299,B_300)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2732,plain,(
    ! [B_300] :
      ( k3_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5',k3_subset_1(k2_struct_0('#skF_5'),B_300))) = k1_tops_1('#skF_5',B_300)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_2700])).

tff(c_2745,plain,(
    ! [B_301] :
      ( k3_subset_1(k2_struct_0('#skF_5'),k2_pre_topc('#skF_5',k3_subset_1(k2_struct_0('#skF_5'),B_301))) = k1_tops_1('#skF_5',B_301)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_211,c_211,c_2732])).

tff(c_2767,plain,
    ( k3_subset_1(k2_struct_0('#skF_5'),k2_pre_topc('#skF_5',k1_xboole_0)) = k1_tops_1('#skF_5',k2_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_2745])).

tff(c_2778,plain,(
    k1_tops_1('#skF_5',k2_struct_0('#skF_5')) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_1185,c_1734,c_2767])).

tff(c_2780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2778])).

tff(c_2781,plain,(
    ! [B_116] : ~ r1_xboole_0(k1_xboole_0,B_116) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_216,plain,(
    ! [A_80,B_81] : r1_xboole_0(k4_xboole_0(A_80,B_81),k4_xboole_0(B_81,A_80)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_219,plain,(
    ! [A_22] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_22,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_216])).

tff(c_2783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2781,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:07:22 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.85  
% 4.59/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.86  %$ v4_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 4.59/1.86  
% 4.59/1.86  %Foreground sorts:
% 4.59/1.86  
% 4.59/1.86  
% 4.59/1.86  %Background operators:
% 4.59/1.86  
% 4.59/1.86  
% 4.59/1.86  %Foreground operators:
% 4.59/1.86  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.59/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.59/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.59/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.59/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.59/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.59/1.86  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.59/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.59/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.59/1.86  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.59/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.59/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.59/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.59/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.59/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.59/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.59/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.59/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.59/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.86  
% 4.59/1.87  tff(f_204, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 4.59/1.87  tff(f_126, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.59/1.87  tff(f_106, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 4.59/1.87  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.59/1.87  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.59/1.87  tff(f_75, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.59/1.87  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.59/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.59/1.87  tff(f_69, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.59/1.87  tff(f_91, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.59/1.87  tff(f_95, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 4.59/1.87  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.59/1.87  tff(f_119, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.59/1.87  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.59/1.87  tff(f_141, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.59/1.87  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.59/1.87  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.59/1.87  tff(f_158, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 4.59/1.87  tff(f_166, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.59/1.87  tff(f_162, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.59/1.87  tff(f_190, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.59/1.87  tff(f_130, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.59/1.87  tff(f_197, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 4.59/1.87  tff(f_87, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 4.59/1.87  tff(c_88, plain, (k1_tops_1('#skF_5', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.59/1.87  tff(c_60, plain, (![A_43]: (~v1_xboole_0(k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.59/1.87  tff(c_48, plain, (![A_38]: (r1_tarski(k1_tarski(A_38), k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.59/1.87  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.59/1.87  tff(c_359, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k4_xboole_0(A_114, B_115))=k3_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.59/1.87  tff(c_28, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.59/1.87  tff(c_407, plain, (![B_116]: (k3_xboole_0(k1_xboole_0, B_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_359, c_28])).
% 4.59/1.87  tff(c_20, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.87  tff(c_412, plain, (![B_116, C_17]: (~r1_xboole_0(k1_xboole_0, B_116) | ~r2_hidden(C_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_20])).
% 4.59/1.87  tff(c_420, plain, (![C_117]: (~r2_hidden(C_117, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_412])).
% 4.59/1.87  tff(c_437, plain, (![B_9]: (r1_xboole_0(k1_xboole_0, B_9))), inference(resolution, [status(thm)], [c_16, c_420])).
% 4.59/1.87  tff(c_115, plain, (![B_75, A_76]: (k2_xboole_0(B_75, A_76)=k2_xboole_0(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.59/1.87  tff(c_22, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.87  tff(c_131, plain, (![A_76]: (k2_xboole_0(k1_xboole_0, A_76)=A_76)), inference(superposition, [status(thm), theory('equality')], [c_115, c_22])).
% 4.59/1.87  tff(c_535, plain, (![A_138, B_139]: (k4_xboole_0(k2_xboole_0(A_138, B_139), B_139)=A_138 | ~r1_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.59/1.87  tff(c_553, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_76))), inference(superposition, [status(thm), theory('equality')], [c_131, c_535])).
% 4.59/1.87  tff(c_643, plain, (![A_144]: (k4_xboole_0(A_144, A_144)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_553])).
% 4.59/1.87  tff(c_38, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | k4_xboole_0(k1_tarski(A_32), B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.87  tff(c_757, plain, (![A_147]: (r2_hidden(A_147, k1_tarski(A_147)))), inference(superposition, [status(thm), theory('equality')], [c_643, c_38])).
% 4.59/1.87  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.59/1.87  tff(c_949, plain, (![A_161, B_162]: (r2_hidden(A_161, B_162) | ~r1_tarski(k1_tarski(A_161), B_162))), inference(resolution, [status(thm)], [c_757, c_4])).
% 4.59/1.87  tff(c_960, plain, (![A_163]: (r2_hidden(A_163, k1_zfmisc_1(A_163)))), inference(resolution, [status(thm)], [c_48, c_949])).
% 4.59/1.87  tff(c_50, plain, (![B_40, A_39]: (m1_subset_1(B_40, A_39) | ~r2_hidden(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.59/1.87  tff(c_965, plain, (![A_163]: (m1_subset_1(A_163, k1_zfmisc_1(A_163)) | v1_xboole_0(k1_zfmisc_1(A_163)))), inference(resolution, [status(thm)], [c_960, c_50])).
% 4.59/1.87  tff(c_969, plain, (![A_163]: (m1_subset_1(A_163, k1_zfmisc_1(A_163)))), inference(negUnitSimplification, [status(thm)], [c_60, c_965])).
% 4.59/1.87  tff(c_30, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.59/1.87  tff(c_562, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18 | ~r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_535])).
% 4.59/1.87  tff(c_568, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_562])).
% 4.59/1.87  tff(c_68, plain, (![A_50]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.59/1.87  tff(c_1147, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=k3_subset_1(A_183, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.59/1.87  tff(c_1175, plain, (![A_50]: (k4_xboole_0(A_50, k1_xboole_0)=k3_subset_1(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_68, c_1147])).
% 4.59/1.87  tff(c_1185, plain, (![A_50]: (k3_subset_1(A_50, k1_xboole_0)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_568, c_1175])).
% 4.59/1.87  tff(c_92, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.59/1.87  tff(c_90, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.59/1.87  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.59/1.87  tff(c_1676, plain, (![B_217, A_218]: (v4_pre_topc(B_217, A_218) | ~v1_xboole_0(B_217) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.59/1.87  tff(c_1710, plain, (![A_218]: (v4_pre_topc(k1_xboole_0, A_218) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(resolution, [status(thm)], [c_68, c_1676])).
% 4.59/1.87  tff(c_1723, plain, (![A_219]: (v4_pre_topc(k1_xboole_0, A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1710])).
% 4.59/1.87  tff(c_76, plain, (![A_58]: (l1_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.59/1.87  tff(c_200, plain, (![A_78]: (u1_struct_0(A_78)=k2_struct_0(A_78) | ~l1_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.87  tff(c_207, plain, (![A_79]: (u1_struct_0(A_79)=k2_struct_0(A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_76, c_200])).
% 4.59/1.87  tff(c_211, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_207])).
% 4.59/1.87  tff(c_1414, plain, (![A_194, B_195]: (k2_pre_topc(A_194, B_195)=B_195 | ~v4_pre_topc(B_195, A_194) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.59/1.87  tff(c_1444, plain, (![B_195]: (k2_pre_topc('#skF_5', B_195)=B_195 | ~v4_pre_topc(B_195, '#skF_5') | ~m1_subset_1(B_195, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_1414])).
% 4.59/1.87  tff(c_1461, plain, (![B_197]: (k2_pre_topc('#skF_5', B_197)=B_197 | ~v4_pre_topc(B_197, '#skF_5') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1444])).
% 4.59/1.87  tff(c_1500, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_68, c_1461])).
% 4.59/1.87  tff(c_1501, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_1500])).
% 4.59/1.87  tff(c_1726, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1723, c_1501])).
% 4.59/1.87  tff(c_1733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1726])).
% 4.59/1.87  tff(c_1734, plain, (k2_pre_topc('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1500])).
% 4.59/1.87  tff(c_873, plain, (![A_153, B_154]: (k3_subset_1(A_153, k3_subset_1(A_153, B_154))=B_154 | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.59/1.87  tff(c_886, plain, (![A_50]: (k3_subset_1(A_50, k3_subset_1(A_50, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_873])).
% 4.59/1.87  tff(c_1186, plain, (![A_50]: (k3_subset_1(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_886])).
% 4.59/1.87  tff(c_2700, plain, (![A_299, B_300]: (k3_subset_1(u1_struct_0(A_299), k2_pre_topc(A_299, k3_subset_1(u1_struct_0(A_299), B_300)))=k1_tops_1(A_299, B_300) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.59/1.87  tff(c_2732, plain, (![B_300]: (k3_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', k3_subset_1(k2_struct_0('#skF_5'), B_300)))=k1_tops_1('#skF_5', B_300) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_2700])).
% 4.59/1.87  tff(c_2745, plain, (![B_301]: (k3_subset_1(k2_struct_0('#skF_5'), k2_pre_topc('#skF_5', k3_subset_1(k2_struct_0('#skF_5'), B_301)))=k1_tops_1('#skF_5', B_301) | ~m1_subset_1(B_301, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_211, c_211, c_2732])).
% 4.59/1.87  tff(c_2767, plain, (k3_subset_1(k2_struct_0('#skF_5'), k2_pre_topc('#skF_5', k1_xboole_0))=k1_tops_1('#skF_5', k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_2745])).
% 4.59/1.87  tff(c_2778, plain, (k1_tops_1('#skF_5', k2_struct_0('#skF_5'))=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_1185, c_1734, c_2767])).
% 4.59/1.87  tff(c_2780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2778])).
% 4.59/1.87  tff(c_2781, plain, (![B_116]: (~r1_xboole_0(k1_xboole_0, B_116))), inference(splitRight, [status(thm)], [c_412])).
% 4.59/1.87  tff(c_216, plain, (![A_80, B_81]: (r1_xboole_0(k4_xboole_0(A_80, B_81), k4_xboole_0(B_81, A_80)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.59/1.87  tff(c_219, plain, (![A_22]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_22, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_216])).
% 4.59/1.87  tff(c_2783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2781, c_219])).
% 4.59/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.87  
% 4.59/1.87  Inference rules
% 4.59/1.87  ----------------------
% 4.59/1.87  #Ref     : 1
% 4.59/1.87  #Sup     : 617
% 4.59/1.87  #Fact    : 0
% 4.59/1.87  #Define  : 0
% 4.59/1.87  #Split   : 5
% 4.59/1.87  #Chain   : 0
% 4.59/1.87  #Close   : 0
% 4.59/1.87  
% 4.59/1.87  Ordering : KBO
% 4.59/1.87  
% 4.59/1.87  Simplification rules
% 4.59/1.87  ----------------------
% 4.59/1.87  #Subsume      : 84
% 4.59/1.87  #Demod        : 240
% 4.59/1.87  #Tautology    : 232
% 4.59/1.87  #SimpNegUnit  : 13
% 4.59/1.87  #BackRed      : 4
% 4.59/1.87  
% 4.59/1.87  #Partial instantiations: 0
% 4.59/1.87  #Strategies tried      : 1
% 4.59/1.87  
% 4.59/1.87  Timing (in seconds)
% 4.59/1.87  ----------------------
% 4.59/1.88  Preprocessing        : 0.39
% 4.59/1.88  Parsing              : 0.20
% 4.59/1.88  CNF conversion       : 0.03
% 4.59/1.88  Main loop            : 0.74
% 4.59/1.88  Inferencing          : 0.25
% 4.59/1.88  Reduction            : 0.24
% 4.59/1.88  Demodulation         : 0.17
% 4.59/1.88  BG Simplification    : 0.04
% 4.59/1.88  Subsumption          : 0.14
% 4.59/1.88  Abstraction          : 0.04
% 4.59/1.88  MUC search           : 0.00
% 4.59/1.88  Cooper               : 0.00
% 4.59/1.88  Total                : 1.16
% 4.59/1.88  Index Insertion      : 0.00
% 4.59/1.88  Index Deletion       : 0.00
% 4.59/1.88  Index Matching       : 0.00
% 4.59/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
