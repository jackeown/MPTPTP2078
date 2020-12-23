%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 513 expanded)
%              Number of leaves         :   39 ( 184 expanded)
%              Depth                    :   19
%              Number of atoms          :  126 ( 884 expanded)
%              Number of equality atoms :   27 ( 193 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_68,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_20] : m1_subset_1(k2_subset_1(A_20),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [A_20] : m1_subset_1(A_20,k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [A_29] :
      ( v1_xboole_0(k1_struct_0(A_29))
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_149,plain,(
    ! [A_69,A_70] :
      ( ~ v1_xboole_0(A_69)
      | ~ r2_hidden(A_70,A_69) ) ),
    inference(resolution,[status(thm)],[c_53,c_142])).

tff(c_170,plain,(
    ! [A_73,B_74] :
      ( ~ v1_xboole_0(A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_22,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_188,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_170,c_22])).

tff(c_201,plain,(
    ! [A_80] :
      ( k1_struct_0(A_80) = k1_xboole_0
      | ~ l1_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_44,c_188])).

tff(c_215,plain,(
    ! [A_83] :
      ( k1_struct_0(A_83) = k1_xboole_0
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_42,c_201])).

tff(c_219,plain,(
    k1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_215])).

tff(c_226,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_44])).

tff(c_230,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_233])).

tff(c_238,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | r1_xboole_0(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_10,c_149])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_307,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,B_91) = A_90
      | ~ v1_xboole_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_162,c_24])).

tff(c_312,plain,(
    ! [A_90] : k4_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(resolution,[status(thm)],[c_238,c_307])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_179,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_563,plain,(
    ! [B_124,A_125] :
      ( k4_xboole_0(B_124,A_125) = k3_subset_1(B_124,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_575,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_563])).

tff(c_583,plain,(
    ! [A_126] : k3_subset_1(A_126,k1_xboole_0) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_575])).

tff(c_239,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_46,plain,(
    ! [A_30] :
      ( k3_subset_1(u1_struct_0(A_30),k1_struct_0(A_30)) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_223,plain,
    ( k3_subset_1(u1_struct_0('#skF_3'),k1_xboole_0) = k2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_46])).

tff(c_282,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k1_xboole_0) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_223])).

tff(c_589,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_282])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_pre_topc(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_609,plain,(
    ! [B_27] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_27),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_40])).

tff(c_807,plain,(
    ! [B_143] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_143),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_589,c_609])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_947,plain,(
    ! [B_157] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_157),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_807,c_34])).

tff(c_50,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_206,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,k2_pre_topc(A_82,B_81))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_214,plain,(
    ! [A_82] :
      ( r1_tarski(u1_struct_0(A_82),k2_pre_topc(A_82,u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_53,c_206])).

tff(c_603,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_214])).

tff(c_618,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_589,c_603])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_642,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_pre_topc('#skF_3',k2_struct_0('#skF_3')),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_618,c_14])).

tff(c_652,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3',k2_struct_0('#skF_3')),k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_642])).

tff(c_950,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_947,c_652])).

tff(c_968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:06:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.49  
% 3.11/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 3.11/1.49  
% 3.11/1.49  %Foreground sorts:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Background operators:
% 3.11/1.49  
% 3.11/1.49  
% 3.11/1.49  %Foreground operators:
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.11/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.11/1.49  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.11/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.11/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.11/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.49  
% 3.24/1.51  tff(f_68, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.24/1.51  tff(f_74, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.24/1.51  tff(f_115, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 3.24/1.51  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.24/1.51  tff(f_99, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 3.24/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.51  tff(f_85, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.24/1.51  tff(f_62, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.24/1.51  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.24/1.51  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.24/1.51  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.24/1.51  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.24/1.51  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.24/1.51  tff(f_103, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 3.24/1.51  tff(f_91, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.24/1.51  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.24/1.51  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.51  tff(c_28, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.51  tff(c_32, plain, (![A_20]: (m1_subset_1(k2_subset_1(A_20), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.24/1.51  tff(c_53, plain, (![A_20]: (m1_subset_1(A_20, k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.24/1.51  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.24/1.51  tff(c_42, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.51  tff(c_44, plain, (![A_29]: (v1_xboole_0(k1_struct_0(A_29)) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.51  tff(c_142, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.24/1.51  tff(c_149, plain, (![A_69, A_70]: (~v1_xboole_0(A_69) | ~r2_hidden(A_70, A_69))), inference(resolution, [status(thm)], [c_53, c_142])).
% 3.24/1.51  tff(c_170, plain, (![A_73, B_74]: (~v1_xboole_0(A_73) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_149])).
% 3.24/1.51  tff(c_22, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.51  tff(c_188, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_170, c_22])).
% 3.24/1.51  tff(c_201, plain, (![A_80]: (k1_struct_0(A_80)=k1_xboole_0 | ~l1_struct_0(A_80))), inference(resolution, [status(thm)], [c_44, c_188])).
% 3.24/1.51  tff(c_215, plain, (![A_83]: (k1_struct_0(A_83)=k1_xboole_0 | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_42, c_201])).
% 3.24/1.51  tff(c_219, plain, (k1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_215])).
% 3.24/1.51  tff(c_226, plain, (v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_219, c_44])).
% 3.24/1.51  tff(c_230, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_226])).
% 3.24/1.51  tff(c_233, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_230])).
% 3.24/1.51  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_233])).
% 3.24/1.51  tff(c_238, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_226])).
% 3.24/1.51  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.24/1.51  tff(c_162, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | r1_xboole_0(A_72, B_71))), inference(resolution, [status(thm)], [c_10, c_149])).
% 3.24/1.51  tff(c_24, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.51  tff(c_307, plain, (![A_90, B_91]: (k4_xboole_0(A_90, B_91)=A_90 | ~v1_xboole_0(B_91))), inference(resolution, [status(thm)], [c_162, c_24])).
% 3.24/1.51  tff(c_312, plain, (![A_90]: (k4_xboole_0(A_90, k1_xboole_0)=A_90)), inference(resolution, [status(thm)], [c_238, c_307])).
% 3.24/1.51  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.51  tff(c_36, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.24/1.51  tff(c_179, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.24/1.51  tff(c_563, plain, (![B_124, A_125]: (k4_xboole_0(B_124, A_125)=k3_subset_1(B_124, A_125) | ~r1_tarski(A_125, B_124))), inference(resolution, [status(thm)], [c_36, c_179])).
% 3.24/1.51  tff(c_575, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_563])).
% 3.24/1.51  tff(c_583, plain, (![A_126]: (k3_subset_1(A_126, k1_xboole_0)=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_575])).
% 3.24/1.51  tff(c_239, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_226])).
% 3.24/1.51  tff(c_46, plain, (![A_30]: (k3_subset_1(u1_struct_0(A_30), k1_struct_0(A_30))=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.24/1.51  tff(c_223, plain, (k3_subset_1(u1_struct_0('#skF_3'), k1_xboole_0)=k2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_219, c_46])).
% 3.24/1.51  tff(c_282, plain, (k3_subset_1(u1_struct_0('#skF_3'), k1_xboole_0)=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_223])).
% 3.24/1.51  tff(c_589, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_583, c_282])).
% 3.24/1.51  tff(c_40, plain, (![A_26, B_27]: (m1_subset_1(k2_pre_topc(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.24/1.51  tff(c_609, plain, (![B_27]: (m1_subset_1(k2_pre_topc('#skF_3', B_27), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_589, c_40])).
% 3.24/1.51  tff(c_807, plain, (![B_143]: (m1_subset_1(k2_pre_topc('#skF_3', B_143), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_589, c_609])).
% 3.24/1.51  tff(c_34, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.24/1.51  tff(c_947, plain, (![B_157]: (r1_tarski(k2_pre_topc('#skF_3', B_157), k2_struct_0('#skF_3')) | ~m1_subset_1(B_157, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_807, c_34])).
% 3.24/1.51  tff(c_50, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.24/1.51  tff(c_206, plain, (![B_81, A_82]: (r1_tarski(B_81, k2_pre_topc(A_82, B_81)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.24/1.51  tff(c_214, plain, (![A_82]: (r1_tarski(u1_struct_0(A_82), k2_pre_topc(A_82, u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_53, c_206])).
% 3.24/1.51  tff(c_603, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_589, c_214])).
% 3.24/1.51  tff(c_618, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_589, c_603])).
% 3.24/1.51  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.51  tff(c_642, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~r1_tarski(k2_pre_topc('#skF_3', k2_struct_0('#skF_3')), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_618, c_14])).
% 3.24/1.51  tff(c_652, plain, (~r1_tarski(k2_pre_topc('#skF_3', k2_struct_0('#skF_3')), k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_642])).
% 3.24/1.51  tff(c_950, plain, (~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_947, c_652])).
% 3.24/1.51  tff(c_968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_950])).
% 3.24/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.51  
% 3.24/1.51  Inference rules
% 3.24/1.51  ----------------------
% 3.24/1.51  #Ref     : 0
% 3.24/1.51  #Sup     : 217
% 3.24/1.51  #Fact    : 0
% 3.24/1.51  #Define  : 0
% 3.24/1.51  #Split   : 3
% 3.24/1.51  #Chain   : 0
% 3.24/1.51  #Close   : 0
% 3.24/1.51  
% 3.24/1.51  Ordering : KBO
% 3.24/1.51  
% 3.24/1.51  Simplification rules
% 3.24/1.51  ----------------------
% 3.24/1.51  #Subsume      : 61
% 3.24/1.51  #Demod        : 68
% 3.24/1.51  #Tautology    : 81
% 3.24/1.51  #SimpNegUnit  : 6
% 3.24/1.51  #BackRed      : 5
% 3.24/1.51  
% 3.24/1.51  #Partial instantiations: 0
% 3.24/1.51  #Strategies tried      : 1
% 3.24/1.51  
% 3.24/1.51  Timing (in seconds)
% 3.24/1.51  ----------------------
% 3.24/1.52  Preprocessing        : 0.35
% 3.24/1.52  Parsing              : 0.19
% 3.24/1.52  CNF conversion       : 0.02
% 3.24/1.52  Main loop            : 0.38
% 3.24/1.52  Inferencing          : 0.14
% 3.24/1.52  Reduction            : 0.10
% 3.24/1.52  Demodulation         : 0.07
% 3.24/1.52  BG Simplification    : 0.02
% 3.24/1.52  Subsumption          : 0.08
% 3.24/1.52  Abstraction          : 0.02
% 3.24/1.52  MUC search           : 0.00
% 3.24/1.52  Cooper               : 0.00
% 3.24/1.52  Total                : 0.76
% 3.24/1.52  Index Insertion      : 0.00
% 3.24/1.52  Index Deletion       : 0.00
% 3.24/1.52  Index Matching       : 0.00
% 3.24/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
