%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 19.68s
% Output     : CNFRefutation 19.87s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 235 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 451 expanded)
%              Number of equality atoms :   13 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_33,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_210,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    ! [B_75] : k9_subset_1(u1_struct_0('#skF_1'),B_75,'#skF_3') = k3_xboole_0(B_75,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_230,plain,(
    ! [A_78,C_79,B_80] :
      ( k9_subset_1(A_78,C_79,B_80) = k9_subset_1(A_78,B_80,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_234,plain,(
    ! [B_80] : k9_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_80) ),
    inference(resolution,[status(thm)],[c_26,c_230])).

tff(c_250,plain,(
    ! [B_82] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_82) = k3_xboole_0(B_82,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_234])).

tff(c_219,plain,(
    ! [B_75] : k9_subset_1(u1_struct_0('#skF_1'),B_75,'#skF_2') = k3_xboole_0(B_75,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_257,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_219])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(A_52,k3_xboole_0(B_53,C_54))
      | ~ r1_tarski(A_52,C_54)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1195,plain,(
    ! [A_116,B_117,C_118,A_119] :
      ( r1_tarski(A_116,k3_xboole_0(B_117,C_118))
      | ~ r1_tarski(A_116,A_119)
      | ~ r1_tarski(A_119,C_118)
      | ~ r1_tarski(A_119,B_117) ) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_3060,plain,(
    ! [A_180,B_181,B_182,C_183] :
      ( r1_tarski(k3_xboole_0(A_180,B_181),k3_xboole_0(B_182,C_183))
      | ~ r1_tarski(A_180,C_183)
      | ~ r1_tarski(A_180,B_182) ) ),
    inference(resolution,[status(thm)],[c_2,c_1195])).

tff(c_64,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_44,A_1,B_2] :
      ( r1_tarski(A_44,A_1)
      | ~ r1_tarski(A_44,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_3204,plain,(
    ! [A_185,B_186,B_187,C_188] :
      ( r1_tarski(k3_xboole_0(A_185,B_186),B_187)
      | ~ r1_tarski(A_185,C_188)
      | ~ r1_tarski(A_185,B_187) ) ),
    inference(resolution,[status(thm)],[c_3060,c_73])).

tff(c_3337,plain,(
    ! [B_189,B_190] :
      ( r1_tarski(k3_xboole_0('#skF_2',B_189),B_190)
      | ~ r1_tarski('#skF_2',B_190) ) ),
    inference(resolution,[status(thm)],[c_45,c_3204])).

tff(c_3400,plain,(
    ! [B_190] :
      ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),B_190)
      | ~ r1_tarski('#skF_2',B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_3337])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_23,B_27,C_29] :
      ( r1_tarski(k2_pre_topc(A_23,B_27),k2_pre_topc(A_23,C_29))
      | ~ r1_tarski(B_27,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_301,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_377,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k2_pre_topc(A_86,B_87),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( k9_subset_1(A_14,B_15,C_16) = k3_xboole_0(B_15,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1547,plain,(
    ! [A_130,B_131,B_132] :
      ( k9_subset_1(u1_struct_0(A_130),B_131,k2_pre_topc(A_130,B_132)) = k3_xboole_0(B_131,k2_pre_topc(A_130,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_377,c_12])).

tff(c_1554,plain,(
    ! [B_131] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_131,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_131,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1547])).

tff(c_1561,plain,(
    ! [B_131] : k9_subset_1(u1_struct_0('#skF_1'),B_131,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_131,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1554])).

tff(c_24,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_220,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_24])).

tff(c_400,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_220])).

tff(c_1942,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_400])).

tff(c_3639,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_1942])).

tff(c_41377,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3639])).

tff(c_41380,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_41377])).

tff(c_41383,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_301,c_41380])).

tff(c_41387,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_41383])).

tff(c_41396,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3400,c_41387])).

tff(c_41421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_41396])).

tff(c_41422,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3639])).

tff(c_41572,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_41422])).

tff(c_41575,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_2,c_41572])).

tff(c_41579,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_41575])).

tff(c_41588,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3400,c_41579])).

tff(c_41613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_41588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.68/10.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.68/10.59  
% 19.68/10.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.87/10.59  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 19.87/10.59  
% 19.87/10.59  %Foreground sorts:
% 19.87/10.59  
% 19.87/10.59  
% 19.87/10.59  %Background operators:
% 19.87/10.59  
% 19.87/10.59  
% 19.87/10.59  %Foreground operators:
% 19.87/10.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.87/10.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.87/10.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.87/10.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.87/10.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.87/10.59  tff('#skF_2', type, '#skF_2': $i).
% 19.87/10.59  tff('#skF_3', type, '#skF_3': $i).
% 19.87/10.59  tff('#skF_1', type, '#skF_1': $i).
% 19.87/10.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.87/10.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.87/10.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.87/10.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.87/10.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.87/10.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 19.87/10.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.87/10.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.87/10.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.87/10.59  
% 19.87/10.61  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 19.87/10.61  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 19.87/10.61  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.87/10.61  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 19.87/10.61  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.87/10.61  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 19.87/10.61  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 19.87/10.61  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 19.87/10.61  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 19.87/10.61  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.87/10.61  tff(c_33, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.87/10.61  tff(c_45, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_33])).
% 19.87/10.61  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.87/10.61  tff(c_210, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.87/10.61  tff(c_218, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_1'), B_75, '#skF_3')=k3_xboole_0(B_75, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_210])).
% 19.87/10.61  tff(c_230, plain, (![A_78, C_79, B_80]: (k9_subset_1(A_78, C_79, B_80)=k9_subset_1(A_78, B_80, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.87/10.61  tff(c_234, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_80))), inference(resolution, [status(thm)], [c_26, c_230])).
% 19.87/10.61  tff(c_250, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_82)=k3_xboole_0(B_82, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_234])).
% 19.87/10.61  tff(c_219, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_1'), B_75, '#skF_2')=k3_xboole_0(B_75, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_210])).
% 19.87/10.61  tff(c_257, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_250, c_219])).
% 19.87/10.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.87/10.61  tff(c_88, plain, (![A_52, B_53, C_54]: (r1_tarski(A_52, k3_xboole_0(B_53, C_54)) | ~r1_tarski(A_52, C_54) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.87/10.61  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.87/10.61  tff(c_1195, plain, (![A_116, B_117, C_118, A_119]: (r1_tarski(A_116, k3_xboole_0(B_117, C_118)) | ~r1_tarski(A_116, A_119) | ~r1_tarski(A_119, C_118) | ~r1_tarski(A_119, B_117))), inference(resolution, [status(thm)], [c_88, c_6])).
% 19.87/10.61  tff(c_3060, plain, (![A_180, B_181, B_182, C_183]: (r1_tarski(k3_xboole_0(A_180, B_181), k3_xboole_0(B_182, C_183)) | ~r1_tarski(A_180, C_183) | ~r1_tarski(A_180, B_182))), inference(resolution, [status(thm)], [c_2, c_1195])).
% 19.87/10.61  tff(c_64, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.87/10.61  tff(c_73, plain, (![A_44, A_1, B_2]: (r1_tarski(A_44, A_1) | ~r1_tarski(A_44, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_64])).
% 19.87/10.61  tff(c_3204, plain, (![A_185, B_186, B_187, C_188]: (r1_tarski(k3_xboole_0(A_185, B_186), B_187) | ~r1_tarski(A_185, C_188) | ~r1_tarski(A_185, B_187))), inference(resolution, [status(thm)], [c_3060, c_73])).
% 19.87/10.61  tff(c_3337, plain, (![B_189, B_190]: (r1_tarski(k3_xboole_0('#skF_2', B_189), B_190) | ~r1_tarski('#skF_2', B_190))), inference(resolution, [status(thm)], [c_45, c_3204])).
% 19.87/10.61  tff(c_3400, plain, (![B_190]: (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), B_190) | ~r1_tarski('#skF_2', B_190))), inference(superposition, [status(thm), theory('equality')], [c_257, c_3337])).
% 19.87/10.61  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.87/10.61  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.87/10.61  tff(c_22, plain, (![A_23, B_27, C_29]: (r1_tarski(k2_pre_topc(A_23, B_27), k2_pre_topc(A_23, C_29)) | ~r1_tarski(B_27, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.87/10.61  tff(c_301, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_257, c_2])).
% 19.87/10.61  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.87/10.61  tff(c_377, plain, (![A_86, B_87]: (m1_subset_1(k2_pre_topc(A_86, B_87), k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.87/10.61  tff(c_12, plain, (![A_14, B_15, C_16]: (k9_subset_1(A_14, B_15, C_16)=k3_xboole_0(B_15, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.87/10.61  tff(c_1547, plain, (![A_130, B_131, B_132]: (k9_subset_1(u1_struct_0(A_130), B_131, k2_pre_topc(A_130, B_132))=k3_xboole_0(B_131, k2_pre_topc(A_130, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_377, c_12])).
% 19.87/10.61  tff(c_1554, plain, (![B_131]: (k9_subset_1(u1_struct_0('#skF_1'), B_131, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_131, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1547])).
% 19.87/10.61  tff(c_1561, plain, (![B_131]: (k9_subset_1(u1_struct_0('#skF_1'), B_131, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_131, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1554])).
% 19.87/10.61  tff(c_24, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.87/10.61  tff(c_220, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_24])).
% 19.87/10.61  tff(c_400, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_220])).
% 19.87/10.61  tff(c_1942, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_400])).
% 19.87/10.61  tff(c_3639, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_1942])).
% 19.87/10.61  tff(c_41377, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3639])).
% 19.87/10.61  tff(c_41380, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_41377])).
% 19.87/10.61  tff(c_41383, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_301, c_41380])).
% 19.87/10.61  tff(c_41387, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_41383])).
% 19.87/10.61  tff(c_41396, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3400, c_41387])).
% 19.87/10.61  tff(c_41421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_41396])).
% 19.87/10.61  tff(c_41422, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_3639])).
% 19.87/10.61  tff(c_41572, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_41422])).
% 19.87/10.61  tff(c_41575, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_2, c_41572])).
% 19.87/10.61  tff(c_41579, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_41575])).
% 19.87/10.61  tff(c_41588, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3400, c_41579])).
% 19.87/10.61  tff(c_41613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_41588])).
% 19.87/10.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.87/10.61  
% 19.87/10.61  Inference rules
% 19.87/10.61  ----------------------
% 19.87/10.61  #Ref     : 0
% 19.87/10.61  #Sup     : 10204
% 19.87/10.61  #Fact    : 0
% 19.87/10.61  #Define  : 0
% 19.87/10.61  #Split   : 13
% 19.87/10.61  #Chain   : 0
% 19.87/10.61  #Close   : 0
% 19.87/10.61  
% 19.87/10.61  Ordering : KBO
% 19.87/10.61  
% 19.87/10.61  Simplification rules
% 19.87/10.61  ----------------------
% 19.87/10.61  #Subsume      : 3133
% 19.87/10.61  #Demod        : 3039
% 19.87/10.61  #Tautology    : 1515
% 19.87/10.61  #SimpNegUnit  : 12
% 19.87/10.61  #BackRed      : 3
% 19.87/10.61  
% 19.87/10.61  #Partial instantiations: 0
% 19.87/10.61  #Strategies tried      : 1
% 19.87/10.61  
% 19.87/10.61  Timing (in seconds)
% 19.87/10.61  ----------------------
% 19.87/10.61  Preprocessing        : 0.31
% 19.87/10.61  Parsing              : 0.17
% 19.87/10.61  CNF conversion       : 0.02
% 19.87/10.61  Main loop            : 9.53
% 19.87/10.61  Inferencing          : 1.25
% 19.87/10.61  Reduction            : 4.68
% 19.87/10.61  Demodulation         : 3.94
% 19.87/10.61  BG Simplification    : 0.15
% 19.87/10.61  Subsumption          : 2.97
% 19.87/10.61  Abstraction          : 0.23
% 19.87/10.61  MUC search           : 0.00
% 19.87/10.61  Cooper               : 0.00
% 19.87/10.61  Total                : 9.87
% 19.87/10.61  Index Insertion      : 0.00
% 19.87/10.61  Index Deletion       : 0.00
% 19.87/10.61  Index Matching       : 0.00
% 19.87/10.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
