%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:53 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 207 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 ( 797 expanded)
%              Number of equality atoms :   12 (  66 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_connsp_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_setfam_1 > k1_connsp_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_connsp_1,type,(
    v2_connsp_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_connsp_1,type,(
    k1_connsp_1: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ( C = D
                     => r1_tarski(k1_connsp_1(B,D),k1_connsp_1(A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_connsp_2)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_connsp_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k1_connsp_1(A,B))
        & v2_connsp_1(k1_connsp_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_connsp_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( C = D
                   => ( v2_connsp_1(C,A)
                    <=> v2_connsp_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_connsp_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k1_connsp_1(A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                    & ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(E,D)
                        <=> ( v2_connsp_1(E,A)
                            & r2_hidden(B,E) ) ) )
                    & k5_setfam_1(u1_struct_0(A),D) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_79,plain,(
    ! [B_108,A_109] :
      ( v2_pre_topc(B_108)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_85,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_82])).

tff(c_72,plain,(
    ! [B_106,A_107] :
      ( l1_pre_topc(B_106)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_72])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_75])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    ! [B_90,A_88] :
      ( r2_hidden(B_90,k1_connsp_1(A_88,B_90))
      | ~ m1_subset_1(B_90,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_connsp_1(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(B_120)))
      | ~ m1_pre_topc(B_120,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_107,plain,(
    ! [A_57,B_58,A_119] :
      ( m1_subset_1(k1_connsp_1(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(A_57,A_119)
      | ~ l1_pre_topc(A_119)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_32,plain,(
    ! [A_62,B_63] :
      ( v2_connsp_1(k1_connsp_1(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_113,plain,(
    ! [D_126,A_127,B_128] :
      ( v2_connsp_1(D_126,A_127)
      | ~ v2_connsp_1(D_126,B_128)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(B_128)))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_pre_topc(B_128,A_127)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_394,plain,(
    ! [A_202,B_203,A_204] :
      ( v2_connsp_1(k1_connsp_1(A_202,B_203),A_204)
      | ~ v2_connsp_1(k1_connsp_1(A_202,B_203),A_202)
      | ~ m1_subset_1(k1_connsp_1(A_202,B_203),k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_pre_topc(A_202,A_204)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202) ) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_409,plain,(
    ! [A_205,B_206,A_207] :
      ( v2_connsp_1(k1_connsp_1(A_205,B_206),A_207)
      | ~ m1_subset_1(k1_connsp_1(A_205,B_206),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_pre_topc(A_205,A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_32,c_394])).

tff(c_426,plain,(
    ! [A_57,B_58,A_119] :
      ( v2_connsp_1(k1_connsp_1(A_57,B_58),A_119)
      | ~ v2_pre_topc(A_119)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57)
      | ~ m1_pre_topc(A_57,A_119)
      | ~ l1_pre_topc(A_119)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_107,c_409])).

tff(c_50,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_65,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_341,plain,(
    ! [E_187,A_188,B_189] :
      ( r2_hidden(E_187,'#skF_1'(A_188,B_189,k1_connsp_1(A_188,B_189)))
      | ~ r2_hidden(B_189,E_187)
      | ~ v2_connsp_1(E_187,A_188)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(k1_connsp_1(A_188,B_189),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_359,plain,(
    ! [E_190,A_191,B_192] :
      ( r2_hidden(E_190,'#skF_1'(A_191,B_192,k1_connsp_1(A_191,B_192)))
      | ~ r2_hidden(B_192,E_190)
      | ~ v2_connsp_1(E_190,A_191)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_28,c_341])).

tff(c_127,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132,B_133,k1_connsp_1(A_132,B_133)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_132))))
      | ~ m1_subset_1(k1_connsp_1(A_132,B_133),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_64,B_65] :
      ( k5_setfam_1(A_64,B_65) = k3_tarski(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_295,plain,(
    ! [A_178,B_179] :
      ( k5_setfam_1(u1_struct_0(A_178),'#skF_1'(A_178,B_179,k1_connsp_1(A_178,B_179))) = k3_tarski('#skF_1'(A_178,B_179,k1_connsp_1(A_178,B_179)))
      | ~ m1_subset_1(k1_connsp_1(A_178,B_179),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_127,c_36])).

tff(c_313,plain,(
    ! [A_180,B_181] :
      ( k5_setfam_1(u1_struct_0(A_180),'#skF_1'(A_180,B_181,k1_connsp_1(A_180,B_181))) = k3_tarski('#skF_1'(A_180,B_181,k1_connsp_1(A_180,B_181)))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_28,c_295])).

tff(c_186,plain,(
    ! [A_148,B_149] :
      ( k5_setfam_1(u1_struct_0(A_148),'#skF_1'(A_148,B_149,k1_connsp_1(A_148,B_149))) = k1_connsp_1(A_148,B_149)
      | ~ m1_subset_1(k1_connsp_1(A_148,B_149),k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_203,plain,(
    ! [A_57,B_58] :
      ( k5_setfam_1(u1_struct_0(A_57),'#skF_1'(A_57,B_58,k1_connsp_1(A_57,B_58))) = k1_connsp_1(A_57,B_58)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_28,c_186])).

tff(c_328,plain,(
    ! [A_182,B_183] :
      ( k3_tarski('#skF_1'(A_182,B_183,k1_connsp_1(A_182,B_183))) = k1_connsp_1(A_182,B_183)
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_203])).

tff(c_46,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,k3_tarski(B_92))
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_334,plain,(
    ! [A_91,A_182,B_183] :
      ( r1_tarski(A_91,k1_connsp_1(A_182,B_183))
      | ~ r2_hidden(A_91,'#skF_1'(A_182,B_183,k1_connsp_1(A_182,B_183)))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_46])).

tff(c_370,plain,(
    ! [E_193,A_194,B_195] :
      ( r1_tarski(E_193,k1_connsp_1(A_194,B_195))
      | ~ r2_hidden(B_195,E_193)
      | ~ v2_connsp_1(E_193,A_194)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_subset_1(B_195,u1_struct_0(A_194))
      | ~ l1_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_359,c_334])).

tff(c_597,plain,(
    ! [A_233,B_234,A_235,B_236] :
      ( r1_tarski(k1_connsp_1(A_233,B_234),k1_connsp_1(A_235,B_236))
      | ~ r2_hidden(B_236,k1_connsp_1(A_233,B_234))
      | ~ v2_connsp_1(k1_connsp_1(A_233,B_234),A_235)
      | ~ m1_subset_1(B_236,u1_struct_0(A_235))
      | ~ m1_pre_topc(A_233,A_235)
      | ~ l1_pre_topc(A_235)
      | ~ m1_subset_1(B_234,u1_struct_0(A_233))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_107,c_370])).

tff(c_48,plain,(
    ~ r1_tarski(k1_connsp_1('#skF_4','#skF_6'),k1_connsp_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_66,plain,(
    ~ r1_tarski(k1_connsp_1('#skF_4','#skF_6'),k1_connsp_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_600,plain,
    ( ~ r2_hidden('#skF_6',k1_connsp_1('#skF_4','#skF_6'))
    | ~ v2_connsp_1(k1_connsp_1('#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_597,c_66])).

tff(c_603,plain,
    ( ~ r2_hidden('#skF_6',k1_connsp_1('#skF_4','#skF_6'))
    | ~ v2_connsp_1(k1_connsp_1('#skF_4','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_60,c_56,c_65,c_600])).

tff(c_604,plain,(
    ~ v2_connsp_1(k1_connsp_1('#skF_4','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_610,plain,
    ( ~ v2_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_426,c_604])).

tff(c_626,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_52,c_60,c_56,c_85,c_62,c_610])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_626])).

tff(c_629,plain,(
    ~ r2_hidden('#skF_6',k1_connsp_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_633,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_629])).

tff(c_636,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_78,c_52,c_633])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_636])).

%------------------------------------------------------------------------------
