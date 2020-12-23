%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 167 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 351 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_40,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [A_24] :
      ( v1_xboole_0(k1_struct_0(A_24))
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_47,B_48] :
      ( ~ v1_xboole_0(A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_36,plain,(
    ! [A_25] :
      ( k3_subset_1(u1_struct_0(A_25),k1_struct_0(A_25)) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_279,plain,(
    ! [C_92,A_93,B_94] :
      ( r1_tarski(C_92,k3_subset_1(A_93,B_94))
      | ~ r1_tarski(B_94,k3_subset_1(A_93,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_852,plain,(
    ! [C_169,A_170,A_171] :
      ( r1_tarski(C_169,k3_subset_1(A_170,A_171))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(A_170))
      | ~ m1_subset_1(A_171,k1_zfmisc_1(A_170))
      | ~ v1_xboole_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_102,c_279])).

tff(c_3727,plain,(
    ! [C_460,A_461] :
      ( r1_tarski(C_460,k2_struct_0(A_461))
      | ~ m1_subset_1(C_460,k1_zfmisc_1(u1_struct_0(A_461)))
      | ~ m1_subset_1(k1_struct_0(A_461),k1_zfmisc_1(u1_struct_0(A_461)))
      | ~ v1_xboole_0(k1_struct_0(A_461))
      | ~ l1_struct_0(A_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_852])).

tff(c_3886,plain,(
    ! [A_471] :
      ( r1_tarski(u1_struct_0(A_471),k2_struct_0(A_471))
      | ~ m1_subset_1(k1_struct_0(A_471),k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ v1_xboole_0(k1_struct_0(A_471))
      | ~ l1_struct_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_43,c_3727])).

tff(c_3891,plain,(
    ! [A_472] :
      ( r1_tarski(u1_struct_0(A_472),k2_struct_0(A_472))
      | ~ v1_xboole_0(k1_struct_0(A_472))
      | ~ l1_struct_0(A_472)
      | ~ r1_tarski(k1_struct_0(A_472),u1_struct_0(A_472)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3886])).

tff(c_76,plain,(
    ! [A_43] :
      ( m1_subset_1(k2_struct_0(A_43),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    ! [A_43] :
      ( r1_tarski(k2_struct_0(A_43),u1_struct_0(A_43))
      | ~ l1_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_156,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [A_80,B_81,B_82] :
      ( r2_hidden('#skF_2'(A_80,B_81),B_82)
      | ~ r1_tarski(A_80,B_82)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_398,plain,(
    ! [A_111,B_112,B_113,B_114] :
      ( r2_hidden('#skF_2'(A_111,B_112),B_113)
      | ~ r1_tarski(B_114,B_113)
      | ~ r1_tarski(A_111,B_114)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_223,c_6])).

tff(c_922,plain,(
    ! [A_181,B_182,A_183] :
      ( r2_hidden('#skF_2'(A_181,B_182),u1_struct_0(A_183))
      | ~ r1_tarski(A_181,k2_struct_0(A_183))
      | r1_tarski(A_181,B_182)
      | ~ l1_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_80,c_398])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_935,plain,(
    ! [A_184,A_185] :
      ( ~ r1_tarski(A_184,k2_struct_0(A_185))
      | r1_tarski(A_184,u1_struct_0(A_185))
      | ~ l1_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_922,c_8])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_975,plain,(
    ! [A_185,A_184] :
      ( u1_struct_0(A_185) = A_184
      | ~ r1_tarski(u1_struct_0(A_185),A_184)
      | ~ r1_tarski(A_184,k2_struct_0(A_185))
      | ~ l1_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_935,c_12])).

tff(c_3936,plain,(
    ! [A_472] :
      ( u1_struct_0(A_472) = k2_struct_0(A_472)
      | ~ r1_tarski(k2_struct_0(A_472),k2_struct_0(A_472))
      | ~ v1_xboole_0(k1_struct_0(A_472))
      | ~ l1_struct_0(A_472)
      | ~ r1_tarski(k1_struct_0(A_472),u1_struct_0(A_472)) ) ),
    inference(resolution,[status(thm)],[c_3891,c_975])).

tff(c_3999,plain,(
    ! [A_473] :
      ( u1_struct_0(A_473) = k2_struct_0(A_473)
      | ~ v1_xboole_0(k1_struct_0(A_473))
      | ~ l1_struct_0(A_473)
      | ~ r1_tarski(k1_struct_0(A_473),u1_struct_0(A_473)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3936])).

tff(c_4009,plain,(
    ! [A_474] :
      ( u1_struct_0(A_474) = k2_struct_0(A_474)
      | ~ l1_struct_0(A_474)
      | ~ v1_xboole_0(k1_struct_0(A_474)) ) ),
    inference(resolution,[status(thm)],[c_102,c_3999])).

tff(c_4025,plain,(
    ! [A_477] :
      ( u1_struct_0(A_477) = k2_struct_0(A_477)
      | ~ l1_struct_0(A_477) ) ),
    inference(resolution,[status(thm)],[c_34,c_4009])).

tff(c_4030,plain,(
    ! [A_478] :
      ( u1_struct_0(A_478) = k2_struct_0(A_478)
      | ~ l1_pre_topc(A_478) ) ),
    inference(resolution,[status(thm)],[c_32,c_4025])).

tff(c_4034,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_4030])).

tff(c_236,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_pre_topc(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_243,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_pre_topc(A_83,B_84),u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_236,c_24])).

tff(c_185,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,k2_pre_topc(A_74,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_197,plain,(
    ! [A_75] :
      ( r1_tarski(u1_struct_0(A_75),k2_pre_topc(A_75,u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_43,c_185])).

tff(c_733,plain,(
    ! [A_161] :
      ( k2_pre_topc(A_161,u1_struct_0(A_161)) = u1_struct_0(A_161)
      | ~ r1_tarski(k2_pre_topc(A_161,u1_struct_0(A_161)),u1_struct_0(A_161))
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_197,c_12])).

tff(c_737,plain,(
    ! [A_83] :
      ( k2_pre_topc(A_83,u1_struct_0(A_83)) = u1_struct_0(A_83)
      | ~ m1_subset_1(u1_struct_0(A_83),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_243,c_733])).

tff(c_743,plain,(
    ! [A_83] :
      ( k2_pre_topc(A_83,u1_struct_0(A_83)) = u1_struct_0(A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_737])).

tff(c_4214,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4034,c_743])).

tff(c_4368,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4034,c_4214])).

tff(c_4370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.29  
% 6.67/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_1 > #skF_3 > #skF_2
% 6.67/2.29  
% 6.67/2.29  %Foreground sorts:
% 6.67/2.29  
% 6.67/2.29  
% 6.67/2.29  %Background operators:
% 6.67/2.29  
% 6.67/2.29  
% 6.67/2.29  %Foreground operators:
% 6.67/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.67/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.67/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.67/2.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.67/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.67/2.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.67/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.67/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.67/2.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.67/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.67/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.67/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.67/2.29  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 6.67/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.67/2.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.67/2.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.67/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.67/2.29  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.67/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.67/2.29  
% 6.78/2.30  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 6.78/2.30  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.78/2.30  tff(f_79, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 6.78/2.30  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.78/2.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.78/2.30  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.78/2.30  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.78/2.30  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.78/2.30  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.78/2.30  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 6.78/2.30  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 6.78/2.30  tff(f_71, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 6.78/2.30  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.78/2.31  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 6.78/2.31  tff(c_40, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.78/2.31  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.78/2.31  tff(c_32, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.78/2.31  tff(c_34, plain, (![A_24]: (v1_xboole_0(k1_struct_0(A_24)) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.78/2.31  tff(c_92, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.78/2.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.78/2.31  tff(c_102, plain, (![A_47, B_48]: (~v1_xboole_0(A_47) | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_92, c_2])).
% 6.78/2.31  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.78/2.31  tff(c_26, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.78/2.31  tff(c_18, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.78/2.31  tff(c_20, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.78/2.31  tff(c_43, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 6.78/2.31  tff(c_36, plain, (![A_25]: (k3_subset_1(u1_struct_0(A_25), k1_struct_0(A_25))=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.78/2.31  tff(c_279, plain, (![C_92, A_93, B_94]: (r1_tarski(C_92, k3_subset_1(A_93, B_94)) | ~r1_tarski(B_94, k3_subset_1(A_93, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.78/2.31  tff(c_852, plain, (![C_169, A_170, A_171]: (r1_tarski(C_169, k3_subset_1(A_170, A_171)) | ~m1_subset_1(C_169, k1_zfmisc_1(A_170)) | ~m1_subset_1(A_171, k1_zfmisc_1(A_170)) | ~v1_xboole_0(A_171))), inference(resolution, [status(thm)], [c_102, c_279])).
% 6.78/2.31  tff(c_3727, plain, (![C_460, A_461]: (r1_tarski(C_460, k2_struct_0(A_461)) | ~m1_subset_1(C_460, k1_zfmisc_1(u1_struct_0(A_461))) | ~m1_subset_1(k1_struct_0(A_461), k1_zfmisc_1(u1_struct_0(A_461))) | ~v1_xboole_0(k1_struct_0(A_461)) | ~l1_struct_0(A_461))), inference(superposition, [status(thm), theory('equality')], [c_36, c_852])).
% 6.78/2.31  tff(c_3886, plain, (![A_471]: (r1_tarski(u1_struct_0(A_471), k2_struct_0(A_471)) | ~m1_subset_1(k1_struct_0(A_471), k1_zfmisc_1(u1_struct_0(A_471))) | ~v1_xboole_0(k1_struct_0(A_471)) | ~l1_struct_0(A_471))), inference(resolution, [status(thm)], [c_43, c_3727])).
% 6.78/2.31  tff(c_3891, plain, (![A_472]: (r1_tarski(u1_struct_0(A_472), k2_struct_0(A_472)) | ~v1_xboole_0(k1_struct_0(A_472)) | ~l1_struct_0(A_472) | ~r1_tarski(k1_struct_0(A_472), u1_struct_0(A_472)))), inference(resolution, [status(thm)], [c_26, c_3886])).
% 6.78/2.31  tff(c_76, plain, (![A_43]: (m1_subset_1(k2_struct_0(A_43), k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.78/2.31  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.78/2.31  tff(c_80, plain, (![A_43]: (r1_tarski(k2_struct_0(A_43), u1_struct_0(A_43)) | ~l1_struct_0(A_43))), inference(resolution, [status(thm)], [c_76, c_24])).
% 6.78/2.31  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.78/2.31  tff(c_156, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.78/2.31  tff(c_223, plain, (![A_80, B_81, B_82]: (r2_hidden('#skF_2'(A_80, B_81), B_82) | ~r1_tarski(A_80, B_82) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_10, c_156])).
% 6.78/2.31  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.78/2.31  tff(c_398, plain, (![A_111, B_112, B_113, B_114]: (r2_hidden('#skF_2'(A_111, B_112), B_113) | ~r1_tarski(B_114, B_113) | ~r1_tarski(A_111, B_114) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_223, c_6])).
% 6.78/2.31  tff(c_922, plain, (![A_181, B_182, A_183]: (r2_hidden('#skF_2'(A_181, B_182), u1_struct_0(A_183)) | ~r1_tarski(A_181, k2_struct_0(A_183)) | r1_tarski(A_181, B_182) | ~l1_struct_0(A_183))), inference(resolution, [status(thm)], [c_80, c_398])).
% 6.78/2.31  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.78/2.31  tff(c_935, plain, (![A_184, A_185]: (~r1_tarski(A_184, k2_struct_0(A_185)) | r1_tarski(A_184, u1_struct_0(A_185)) | ~l1_struct_0(A_185))), inference(resolution, [status(thm)], [c_922, c_8])).
% 6.78/2.31  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.78/2.31  tff(c_975, plain, (![A_185, A_184]: (u1_struct_0(A_185)=A_184 | ~r1_tarski(u1_struct_0(A_185), A_184) | ~r1_tarski(A_184, k2_struct_0(A_185)) | ~l1_struct_0(A_185))), inference(resolution, [status(thm)], [c_935, c_12])).
% 6.78/2.31  tff(c_3936, plain, (![A_472]: (u1_struct_0(A_472)=k2_struct_0(A_472) | ~r1_tarski(k2_struct_0(A_472), k2_struct_0(A_472)) | ~v1_xboole_0(k1_struct_0(A_472)) | ~l1_struct_0(A_472) | ~r1_tarski(k1_struct_0(A_472), u1_struct_0(A_472)))), inference(resolution, [status(thm)], [c_3891, c_975])).
% 6.78/2.31  tff(c_3999, plain, (![A_473]: (u1_struct_0(A_473)=k2_struct_0(A_473) | ~v1_xboole_0(k1_struct_0(A_473)) | ~l1_struct_0(A_473) | ~r1_tarski(k1_struct_0(A_473), u1_struct_0(A_473)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3936])).
% 6.78/2.31  tff(c_4009, plain, (![A_474]: (u1_struct_0(A_474)=k2_struct_0(A_474) | ~l1_struct_0(A_474) | ~v1_xboole_0(k1_struct_0(A_474)))), inference(resolution, [status(thm)], [c_102, c_3999])).
% 6.78/2.31  tff(c_4025, plain, (![A_477]: (u1_struct_0(A_477)=k2_struct_0(A_477) | ~l1_struct_0(A_477))), inference(resolution, [status(thm)], [c_34, c_4009])).
% 6.78/2.31  tff(c_4030, plain, (![A_478]: (u1_struct_0(A_478)=k2_struct_0(A_478) | ~l1_pre_topc(A_478))), inference(resolution, [status(thm)], [c_32, c_4025])).
% 6.78/2.31  tff(c_4034, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_4030])).
% 6.78/2.31  tff(c_236, plain, (![A_83, B_84]: (m1_subset_1(k2_pre_topc(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.78/2.31  tff(c_243, plain, (![A_83, B_84]: (r1_tarski(k2_pre_topc(A_83, B_84), u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_236, c_24])).
% 6.78/2.31  tff(c_185, plain, (![B_73, A_74]: (r1_tarski(B_73, k2_pre_topc(A_74, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.78/2.31  tff(c_197, plain, (![A_75]: (r1_tarski(u1_struct_0(A_75), k2_pre_topc(A_75, u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_43, c_185])).
% 6.78/2.31  tff(c_733, plain, (![A_161]: (k2_pre_topc(A_161, u1_struct_0(A_161))=u1_struct_0(A_161) | ~r1_tarski(k2_pre_topc(A_161, u1_struct_0(A_161)), u1_struct_0(A_161)) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_197, c_12])).
% 6.78/2.31  tff(c_737, plain, (![A_83]: (k2_pre_topc(A_83, u1_struct_0(A_83))=u1_struct_0(A_83) | ~m1_subset_1(u1_struct_0(A_83), k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_243, c_733])).
% 6.78/2.31  tff(c_743, plain, (![A_83]: (k2_pre_topc(A_83, u1_struct_0(A_83))=u1_struct_0(A_83) | ~l1_pre_topc(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_737])).
% 6.78/2.31  tff(c_4214, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4034, c_743])).
% 6.78/2.31  tff(c_4368, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4034, c_4214])).
% 6.78/2.31  tff(c_4370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_4368])).
% 6.78/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.31  
% 6.78/2.31  Inference rules
% 6.78/2.31  ----------------------
% 6.78/2.31  #Ref     : 0
% 6.78/2.31  #Sup     : 1083
% 6.78/2.31  #Fact    : 0
% 6.78/2.31  #Define  : 0
% 6.78/2.31  #Split   : 1
% 6.78/2.31  #Chain   : 0
% 6.78/2.31  #Close   : 0
% 6.78/2.31  
% 6.78/2.31  Ordering : KBO
% 6.78/2.31  
% 6.78/2.31  Simplification rules
% 6.78/2.31  ----------------------
% 6.78/2.31  #Subsume      : 436
% 6.78/2.31  #Demod        : 187
% 6.78/2.31  #Tautology    : 77
% 6.78/2.31  #SimpNegUnit  : 1
% 6.78/2.31  #BackRed      : 0
% 6.78/2.31  
% 6.78/2.31  #Partial instantiations: 0
% 6.78/2.31  #Strategies tried      : 1
% 6.78/2.31  
% 6.78/2.31  Timing (in seconds)
% 6.78/2.31  ----------------------
% 6.78/2.31  Preprocessing        : 0.29
% 6.78/2.31  Parsing              : 0.16
% 6.78/2.31  CNF conversion       : 0.02
% 6.78/2.31  Main loop            : 1.24
% 6.78/2.31  Inferencing          : 0.38
% 6.78/2.31  Reduction            : 0.26
% 6.78/2.31  Demodulation         : 0.16
% 6.78/2.31  BG Simplification    : 0.04
% 6.78/2.31  Subsumption          : 0.47
% 6.78/2.31  Abstraction          : 0.05
% 6.78/2.31  MUC search           : 0.00
% 6.78/2.31  Cooper               : 0.00
% 6.78/2.31  Total                : 1.57
% 6.78/2.31  Index Insertion      : 0.00
% 6.78/2.31  Index Deletion       : 0.00
% 6.78/2.31  Index Matching       : 0.00
% 6.78/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
