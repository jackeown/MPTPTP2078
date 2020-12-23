%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:03 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 258 expanded)
%              Number of leaves         :   40 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 439 expanded)
%              Number of equality atoms :   17 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_122,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_76,B_77] : k1_setfam_1(k2_tarski(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,(
    ! [A_83,B_84] : k1_setfam_1(k2_tarski(A_83,B_84)) = k3_xboole_0(B_84,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_107])).

tff(c_30,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    ! [B_84,A_83] : k3_xboole_0(B_84,A_83) = k3_xboole_0(A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_30])).

tff(c_22,plain,(
    ! [A_37] : k2_subset_1(A_37) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_38] : m1_subset_1(k2_subset_1(A_38),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51,plain,(
    ! [A_38] : m1_subset_1(A_38,k1_zfmisc_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_138,plain,(
    ! [A_38] : r1_tarski(A_38,A_38) ),
    inference(resolution,[status(thm)],[c_51,c_122])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_zfmisc_1(A_35),k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_253,plain,(
    ! [A_105,B_106,A_107] :
      ( m1_subset_1(A_105,B_106)
      | ~ r2_hidden(A_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_36,c_224])).

tff(c_331,plain,(
    ! [A_121,B_122,B_123] :
      ( m1_subset_1(A_121,B_122)
      | ~ r1_tarski(B_123,B_122)
      | v1_xboole_0(B_123)
      | ~ m1_subset_1(A_121,B_123) ) ),
    inference(resolution,[status(thm)],[c_32,c_253])).

tff(c_337,plain,(
    ! [A_121,B_36,A_35] :
      ( m1_subset_1(A_121,k1_zfmisc_1(B_36))
      | v1_xboole_0(k1_zfmisc_1(A_35))
      | ~ m1_subset_1(A_121,k1_zfmisc_1(A_35))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_20,c_331])).

tff(c_372,plain,(
    ! [A_127,B_128,A_129] :
      ( m1_subset_1(A_127,k1_zfmisc_1(B_128))
      | ~ m1_subset_1(A_127,k1_zfmisc_1(A_129))
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_337])).

tff(c_418,plain,(
    ! [A_137,B_138,B_139] :
      ( m1_subset_1(A_137,k1_zfmisc_1(B_138))
      | ~ r1_tarski(B_139,B_138)
      | ~ r1_tarski(A_137,B_139) ) ),
    inference(resolution,[status(thm)],[c_36,c_372])).

tff(c_512,plain,(
    ! [A_144,A_145,B_146] :
      ( m1_subset_1(A_144,k1_zfmisc_1(A_145))
      | ~ r1_tarski(A_144,k3_xboole_0(A_145,B_146)) ) ),
    inference(resolution,[status(thm)],[c_2,c_418])).

tff(c_538,plain,(
    ! [A_147,B_148] : m1_subset_1(k3_xboole_0(A_147,B_148),k1_zfmisc_1(A_147)) ),
    inference(resolution,[status(thm)],[c_138,c_512])).

tff(c_350,plain,(
    ! [A_121,B_36,A_35] :
      ( m1_subset_1(A_121,k1_zfmisc_1(B_36))
      | ~ m1_subset_1(A_121,k1_zfmisc_1(A_35))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_337])).

tff(c_1001,plain,(
    ! [A_208,B_209,B_210] :
      ( m1_subset_1(k3_xboole_0(A_208,B_209),k1_zfmisc_1(B_210))
      | ~ r1_tarski(A_208,B_210) ) ),
    inference(resolution,[status(thm)],[c_538,c_350])).

tff(c_1016,plain,(
    ! [A_83,B_84,B_210] :
      ( m1_subset_1(k3_xboole_0(A_83,B_84),k1_zfmisc_1(B_210))
      | ~ r1_tarski(B_84,B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1001])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_164,plain,(
    ! [B_85,A_86] : k3_xboole_0(B_85,A_86) = k3_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_30])).

tff(c_179,plain,(
    ! [B_85,A_86] : r1_tarski(k3_xboole_0(B_85,A_86),A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_2])).

tff(c_42,plain,(
    ! [A_54,B_58,C_60] :
      ( r1_tarski(k2_pre_topc(A_54,B_58),k2_pre_topc(A_54,C_60))
      | ~ r1_tarski(B_58,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_583,plain,(
    ! [A_151,B_152] :
      ( m1_subset_1(k2_pre_topc(A_151,B_152),k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1569,plain,(
    ! [A_271,B_272,B_273] :
      ( k9_subset_1(u1_struct_0(A_271),B_272,k2_pre_topc(A_271,B_273)) = k3_xboole_0(B_272,k2_pre_topc(A_271,B_273))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(resolution,[status(thm)],[c_583,c_28])).

tff(c_1607,plain,(
    ! [B_272] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_272,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_272,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_1569])).

tff(c_1632,plain,(
    ! [B_272] : k9_subset_1(u1_struct_0('#skF_1'),B_272,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_272,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1607])).

tff(c_257,plain,(
    ! [A_108,B_109,C_110] :
      ( k9_subset_1(A_108,B_109,C_110) = k3_xboole_0(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_267,plain,(
    ! [B_109] : k9_subset_1(u1_struct_0('#skF_1'),B_109,'#skF_3') = k3_xboole_0(B_109,'#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_257])).

tff(c_44,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_279,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_44])).

tff(c_280,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_279])).

tff(c_1685,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_280])).

tff(c_1686,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1685])).

tff(c_1866,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1686])).

tff(c_6923,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1866])).

tff(c_6926,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6923])).

tff(c_6929,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2,c_6926])).

tff(c_6932,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1016,c_6929])).

tff(c_6948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_6932])).

tff(c_6949,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1866])).

tff(c_6953,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6949])).

tff(c_6956,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_179,c_6953])).

tff(c_7056,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1016,c_6956])).

tff(c_7072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_7056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.45  
% 6.79/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.79/2.45  
% 6.79/2.45  %Foreground sorts:
% 6.79/2.45  
% 6.79/2.45  
% 6.79/2.45  %Background operators:
% 6.79/2.45  
% 6.79/2.45  
% 6.79/2.45  %Foreground operators:
% 6.79/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.79/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.79/2.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.79/2.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.79/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.79/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.79/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.79/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.79/2.45  tff('#skF_2', type, '#skF_2': $i).
% 6.79/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.79/2.45  tff('#skF_1', type, '#skF_1': $i).
% 6.79/2.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.79/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.79/2.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.79/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.79/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.79/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.79/2.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.79/2.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.79/2.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.79/2.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.79/2.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.79/2.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.79/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.79/2.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.79/2.45  
% 6.79/2.47  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 6.79/2.47  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.79/2.47  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.79/2.47  tff(f_64, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.79/2.47  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.79/2.47  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.79/2.47  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.79/2.47  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.79/2.47  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 6.79/2.47  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.79/2.47  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.79/2.47  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 6.79/2.47  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.79/2.47  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.79/2.47  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.79/2.47  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.79/2.47  tff(c_122, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.79/2.47  tff(c_137, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_122])).
% 6.79/2.47  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.79/2.47  tff(c_107, plain, (![A_76, B_77]: (k1_setfam_1(k2_tarski(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.79/2.47  tff(c_141, plain, (![A_83, B_84]: (k1_setfam_1(k2_tarski(A_83, B_84))=k3_xboole_0(B_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_6, c_107])).
% 6.79/2.47  tff(c_30, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.79/2.47  tff(c_147, plain, (![B_84, A_83]: (k3_xboole_0(B_84, A_83)=k3_xboole_0(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_141, c_30])).
% 6.79/2.47  tff(c_22, plain, (![A_37]: (k2_subset_1(A_37)=A_37)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.79/2.47  tff(c_24, plain, (![A_38]: (m1_subset_1(k2_subset_1(A_38), k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.79/2.47  tff(c_51, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 6.79/2.47  tff(c_138, plain, (![A_38]: (r1_tarski(A_38, A_38))), inference(resolution, [status(thm)], [c_51, c_122])).
% 6.79/2.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.79/2.47  tff(c_36, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.79/2.47  tff(c_26, plain, (![A_39]: (~v1_xboole_0(k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.79/2.47  tff(c_20, plain, (![A_35, B_36]: (r1_tarski(k1_zfmisc_1(A_35), k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.79/2.47  tff(c_32, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.79/2.47  tff(c_224, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.79/2.47  tff(c_253, plain, (![A_105, B_106, A_107]: (m1_subset_1(A_105, B_106) | ~r2_hidden(A_105, A_107) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_36, c_224])).
% 6.79/2.47  tff(c_331, plain, (![A_121, B_122, B_123]: (m1_subset_1(A_121, B_122) | ~r1_tarski(B_123, B_122) | v1_xboole_0(B_123) | ~m1_subset_1(A_121, B_123))), inference(resolution, [status(thm)], [c_32, c_253])).
% 6.79/2.47  tff(c_337, plain, (![A_121, B_36, A_35]: (m1_subset_1(A_121, k1_zfmisc_1(B_36)) | v1_xboole_0(k1_zfmisc_1(A_35)) | ~m1_subset_1(A_121, k1_zfmisc_1(A_35)) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_20, c_331])).
% 6.79/2.47  tff(c_372, plain, (![A_127, B_128, A_129]: (m1_subset_1(A_127, k1_zfmisc_1(B_128)) | ~m1_subset_1(A_127, k1_zfmisc_1(A_129)) | ~r1_tarski(A_129, B_128))), inference(negUnitSimplification, [status(thm)], [c_26, c_337])).
% 6.79/2.47  tff(c_418, plain, (![A_137, B_138, B_139]: (m1_subset_1(A_137, k1_zfmisc_1(B_138)) | ~r1_tarski(B_139, B_138) | ~r1_tarski(A_137, B_139))), inference(resolution, [status(thm)], [c_36, c_372])).
% 6.79/2.47  tff(c_512, plain, (![A_144, A_145, B_146]: (m1_subset_1(A_144, k1_zfmisc_1(A_145)) | ~r1_tarski(A_144, k3_xboole_0(A_145, B_146)))), inference(resolution, [status(thm)], [c_2, c_418])).
% 6.79/2.47  tff(c_538, plain, (![A_147, B_148]: (m1_subset_1(k3_xboole_0(A_147, B_148), k1_zfmisc_1(A_147)))), inference(resolution, [status(thm)], [c_138, c_512])).
% 6.79/2.47  tff(c_350, plain, (![A_121, B_36, A_35]: (m1_subset_1(A_121, k1_zfmisc_1(B_36)) | ~m1_subset_1(A_121, k1_zfmisc_1(A_35)) | ~r1_tarski(A_35, B_36))), inference(negUnitSimplification, [status(thm)], [c_26, c_337])).
% 6.79/2.47  tff(c_1001, plain, (![A_208, B_209, B_210]: (m1_subset_1(k3_xboole_0(A_208, B_209), k1_zfmisc_1(B_210)) | ~r1_tarski(A_208, B_210))), inference(resolution, [status(thm)], [c_538, c_350])).
% 6.79/2.47  tff(c_1016, plain, (![A_83, B_84, B_210]: (m1_subset_1(k3_xboole_0(A_83, B_84), k1_zfmisc_1(B_210)) | ~r1_tarski(B_84, B_210))), inference(superposition, [status(thm), theory('equality')], [c_147, c_1001])).
% 6.79/2.47  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.79/2.47  tff(c_164, plain, (![B_85, A_86]: (k3_xboole_0(B_85, A_86)=k3_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_141, c_30])).
% 6.79/2.47  tff(c_179, plain, (![B_85, A_86]: (r1_tarski(k3_xboole_0(B_85, A_86), A_86))), inference(superposition, [status(thm), theory('equality')], [c_164, c_2])).
% 6.79/2.47  tff(c_42, plain, (![A_54, B_58, C_60]: (r1_tarski(k2_pre_topc(A_54, B_58), k2_pre_topc(A_54, C_60)) | ~r1_tarski(B_58, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.79/2.47  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.79/2.47  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.79/2.47  tff(c_583, plain, (![A_151, B_152]: (m1_subset_1(k2_pre_topc(A_151, B_152), k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.79/2.47  tff(c_28, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.79/2.47  tff(c_1569, plain, (![A_271, B_272, B_273]: (k9_subset_1(u1_struct_0(A_271), B_272, k2_pre_topc(A_271, B_273))=k3_xboole_0(B_272, k2_pre_topc(A_271, B_273)) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(resolution, [status(thm)], [c_583, c_28])).
% 6.79/2.47  tff(c_1607, plain, (![B_272]: (k9_subset_1(u1_struct_0('#skF_1'), B_272, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_272, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_1569])).
% 6.79/2.47  tff(c_1632, plain, (![B_272]: (k9_subset_1(u1_struct_0('#skF_1'), B_272, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_272, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1607])).
% 6.79/2.47  tff(c_257, plain, (![A_108, B_109, C_110]: (k9_subset_1(A_108, B_109, C_110)=k3_xboole_0(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.79/2.47  tff(c_267, plain, (![B_109]: (k9_subset_1(u1_struct_0('#skF_1'), B_109, '#skF_3')=k3_xboole_0(B_109, '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_257])).
% 6.79/2.47  tff(c_44, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.79/2.47  tff(c_279, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_44])).
% 6.79/2.47  tff(c_280, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_279])).
% 6.79/2.47  tff(c_1685, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_280])).
% 6.79/2.47  tff(c_1686, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1685])).
% 6.79/2.47  tff(c_1866, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1686])).
% 6.79/2.47  tff(c_6923, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1866])).
% 6.79/2.47  tff(c_6926, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6923])).
% 6.79/2.47  tff(c_6929, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2, c_6926])).
% 6.79/2.47  tff(c_6932, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1016, c_6929])).
% 6.79/2.47  tff(c_6948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_6932])).
% 6.79/2.47  tff(c_6949, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1866])).
% 6.79/2.47  tff(c_6953, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6949])).
% 6.79/2.47  tff(c_6956, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_179, c_6953])).
% 6.79/2.47  tff(c_7056, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1016, c_6956])).
% 6.79/2.47  tff(c_7072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_7056])).
% 6.79/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.79/2.47  
% 6.79/2.47  Inference rules
% 6.79/2.47  ----------------------
% 6.79/2.47  #Ref     : 0
% 6.79/2.47  #Sup     : 1749
% 6.79/2.47  #Fact    : 0
% 6.79/2.47  #Define  : 0
% 6.79/2.47  #Split   : 6
% 6.79/2.47  #Chain   : 0
% 6.79/2.47  #Close   : 0
% 6.79/2.47  
% 6.79/2.47  Ordering : KBO
% 6.79/2.47  
% 6.79/2.47  Simplification rules
% 6.79/2.47  ----------------------
% 6.79/2.47  #Subsume      : 225
% 6.79/2.47  #Demod        : 636
% 6.79/2.47  #Tautology    : 712
% 6.79/2.47  #SimpNegUnit  : 29
% 6.79/2.47  #BackRed      : 2
% 6.79/2.47  
% 6.79/2.47  #Partial instantiations: 0
% 6.79/2.47  #Strategies tried      : 1
% 6.79/2.47  
% 6.79/2.47  Timing (in seconds)
% 6.79/2.47  ----------------------
% 6.79/2.47  Preprocessing        : 0.32
% 6.79/2.47  Parsing              : 0.17
% 6.79/2.47  CNF conversion       : 0.02
% 6.79/2.47  Main loop            : 1.30
% 6.79/2.47  Inferencing          : 0.38
% 6.79/2.47  Reduction            : 0.56
% 6.79/2.47  Demodulation         : 0.47
% 6.79/2.47  BG Simplification    : 0.05
% 6.79/2.47  Subsumption          : 0.24
% 6.79/2.47  Abstraction          : 0.06
% 6.79/2.47  MUC search           : 0.00
% 6.79/2.47  Cooper               : 0.00
% 6.79/2.47  Total                : 1.66
% 6.79/2.47  Index Insertion      : 0.00
% 6.79/2.47  Index Deletion       : 0.00
% 6.79/2.47  Index Matching       : 0.00
% 6.79/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
