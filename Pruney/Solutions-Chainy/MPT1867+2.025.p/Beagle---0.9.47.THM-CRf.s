%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:25 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 183 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  122 ( 375 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_49,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_181,plain,(
    ! [A_85,B_86] :
      ( r1_tarski('#skF_3'(A_85,B_86),B_86)
      | v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_226,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_3'(A_92,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_66,c_181])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_7] :
      ( A_7 = '#skF_5'
      | ~ r1_tarski(A_7,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_12])).

tff(c_248,plain,(
    ! [A_95] :
      ( '#skF_3'(A_95,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_226,c_75])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_251,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_248,c_38])).

tff(c_254,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_251])).

tff(c_155,plain,(
    ! [B_80,A_81] :
      ( v3_pre_topc(B_80,A_81)
      | ~ v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_167,plain,(
    ! [A_81] :
      ( v3_pre_topc('#skF_5',A_81)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_66,c_155])).

tff(c_172,plain,(
    ! [A_81] :
      ( v3_pre_topc('#skF_5',A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_167])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    ! [A_14,B_71] : k9_subset_1(A_14,B_71,'#skF_5') = k3_xboole_0(B_71,'#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_130,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k9_subset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [B_71,A_14] :
      ( m1_subset_1(k3_xboole_0(B_71,'#skF_5'),k1_zfmisc_1(A_14))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_130])).

tff(c_145,plain,(
    ! [B_78,A_79] : m1_subset_1(k3_xboole_0(B_78,'#skF_5'),k1_zfmisc_1(A_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_139])).

tff(c_22,plain,(
    ! [C_20,B_19,A_18] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    ! [A_79,A_18,B_78] :
      ( ~ v1_xboole_0(A_79)
      | ~ r2_hidden(A_18,k3_xboole_0(B_78,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_145,c_22])).

tff(c_175,plain,(
    ! [A_83,B_84] : ~ r2_hidden(A_83,k3_xboole_0(B_84,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_194,plain,(
    ! [B_87,B_88] : r1_tarski(k3_xboole_0(B_87,'#skF_5'),B_88) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_199,plain,(
    ! [B_87] : k3_xboole_0(B_87,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_194,c_75])).

tff(c_203,plain,(
    ! [A_14,B_71] : k9_subset_1(A_14,B_71,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_120])).

tff(c_361,plain,(
    ! [A_114,B_115,D_116] :
      ( k9_subset_1(u1_struct_0(A_114),B_115,D_116) != '#skF_3'(A_114,B_115)
      | ~ v3_pre_topc(D_116,A_114)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0(A_114)))
      | v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_364,plain,(
    ! [A_114,B_71] :
      ( '#skF_3'(A_114,B_71) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_114)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_114)))
      | v2_tex_2(B_71,A_114)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_361])).

tff(c_579,plain,(
    ! [A_158,B_159] :
      ( '#skF_3'(A_158,B_159) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_158)
      | v2_tex_2(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_364])).

tff(c_598,plain,(
    ! [A_160] :
      ( '#skF_3'(A_160,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_160)
      | v2_tex_2('#skF_5',A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_66,c_579])).

tff(c_603,plain,(
    ! [A_161] :
      ( '#skF_3'(A_161,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_172,c_598])).

tff(c_606,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_603,c_38])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_254,c_606])).

tff(c_611,plain,(
    ! [A_79] : ~ v1_xboole_0(A_79) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.36  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.57/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.57/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.36  
% 2.83/1.38  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.83/1.38  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.83/1.38  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.83/1.38  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.83/1.38  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.83/1.38  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.83/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.38  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.83/1.38  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.83/1.38  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.83/1.38  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_42, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_49, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.38  tff(c_58, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_49])).
% 2.83/1.38  tff(c_18, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.38  tff(c_66, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 2.83/1.38  tff(c_181, plain, (![A_85, B_86]: (r1_tarski('#skF_3'(A_85, B_86), B_86) | v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.38  tff(c_226, plain, (![A_92]: (r1_tarski('#skF_3'(A_92, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_66, c_181])).
% 2.83/1.38  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.38  tff(c_75, plain, (![A_7]: (A_7='#skF_5' | ~r1_tarski(A_7, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_12])).
% 2.83/1.38  tff(c_248, plain, (![A_95]: ('#skF_3'(A_95, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_226, c_75])).
% 2.83/1.38  tff(c_38, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.38  tff(c_251, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_248, c_38])).
% 2.83/1.38  tff(c_254, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_251])).
% 2.83/1.38  tff(c_155, plain, (![B_80, A_81]: (v3_pre_topc(B_80, A_81) | ~v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.83/1.38  tff(c_167, plain, (![A_81]: (v3_pre_topc('#skF_5', A_81) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(resolution, [status(thm)], [c_66, c_155])).
% 2.83/1.38  tff(c_172, plain, (![A_81]: (v3_pre_topc('#skF_5', A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_167])).
% 2.83/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.38  tff(c_117, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.38  tff(c_120, plain, (![A_14, B_71]: (k9_subset_1(A_14, B_71, '#skF_5')=k3_xboole_0(B_71, '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_117])).
% 2.83/1.38  tff(c_130, plain, (![A_75, B_76, C_77]: (m1_subset_1(k9_subset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.38  tff(c_139, plain, (![B_71, A_14]: (m1_subset_1(k3_xboole_0(B_71, '#skF_5'), k1_zfmisc_1(A_14)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_130])).
% 2.83/1.38  tff(c_145, plain, (![B_78, A_79]: (m1_subset_1(k3_xboole_0(B_78, '#skF_5'), k1_zfmisc_1(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_139])).
% 2.83/1.38  tff(c_22, plain, (![C_20, B_19, A_18]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.38  tff(c_154, plain, (![A_79, A_18, B_78]: (~v1_xboole_0(A_79) | ~r2_hidden(A_18, k3_xboole_0(B_78, '#skF_5')))), inference(resolution, [status(thm)], [c_145, c_22])).
% 2.83/1.38  tff(c_175, plain, (![A_83, B_84]: (~r2_hidden(A_83, k3_xboole_0(B_84, '#skF_5')))), inference(splitLeft, [status(thm)], [c_154])).
% 2.83/1.38  tff(c_194, plain, (![B_87, B_88]: (r1_tarski(k3_xboole_0(B_87, '#skF_5'), B_88))), inference(resolution, [status(thm)], [c_6, c_175])).
% 2.83/1.38  tff(c_199, plain, (![B_87]: (k3_xboole_0(B_87, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_194, c_75])).
% 2.83/1.38  tff(c_203, plain, (![A_14, B_71]: (k9_subset_1(A_14, B_71, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_120])).
% 2.83/1.38  tff(c_361, plain, (![A_114, B_115, D_116]: (k9_subset_1(u1_struct_0(A_114), B_115, D_116)!='#skF_3'(A_114, B_115) | ~v3_pre_topc(D_116, A_114) | ~m1_subset_1(D_116, k1_zfmisc_1(u1_struct_0(A_114))) | v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.38  tff(c_364, plain, (![A_114, B_71]: ('#skF_3'(A_114, B_71)!='#skF_5' | ~v3_pre_topc('#skF_5', A_114) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_114))) | v2_tex_2(B_71, A_114) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(superposition, [status(thm), theory('equality')], [c_203, c_361])).
% 2.83/1.38  tff(c_579, plain, (![A_158, B_159]: ('#skF_3'(A_158, B_159)!='#skF_5' | ~v3_pre_topc('#skF_5', A_158) | v2_tex_2(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_364])).
% 2.83/1.38  tff(c_598, plain, (![A_160]: ('#skF_3'(A_160, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_160) | v2_tex_2('#skF_5', A_160) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_66, c_579])).
% 2.83/1.38  tff(c_603, plain, (![A_161]: ('#skF_3'(A_161, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(resolution, [status(thm)], [c_172, c_598])).
% 2.83/1.38  tff(c_606, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_603, c_38])).
% 2.83/1.38  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_254, c_606])).
% 2.83/1.38  tff(c_611, plain, (![A_79]: (~v1_xboole_0(A_79))), inference(splitRight, [status(thm)], [c_154])).
% 2.83/1.38  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_42])).
% 2.83/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.38  
% 2.83/1.38  Inference rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Ref     : 0
% 2.83/1.38  #Sup     : 125
% 2.83/1.38  #Fact    : 0
% 2.83/1.38  #Define  : 0
% 2.83/1.38  #Split   : 2
% 2.83/1.38  #Chain   : 0
% 2.83/1.38  #Close   : 0
% 2.83/1.38  
% 2.83/1.38  Ordering : KBO
% 2.83/1.38  
% 2.83/1.38  Simplification rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Subsume      : 25
% 2.83/1.38  #Demod        : 70
% 2.83/1.38  #Tautology    : 40
% 2.83/1.38  #SimpNegUnit  : 5
% 2.83/1.38  #BackRed      : 7
% 2.83/1.38  
% 2.83/1.38  #Partial instantiations: 0
% 2.83/1.38  #Strategies tried      : 1
% 2.83/1.38  
% 2.83/1.38  Timing (in seconds)
% 2.83/1.38  ----------------------
% 2.83/1.38  Preprocessing        : 0.31
% 2.83/1.38  Parsing              : 0.17
% 2.83/1.38  CNF conversion       : 0.02
% 2.83/1.38  Main loop            : 0.31
% 2.83/1.38  Inferencing          : 0.12
% 2.83/1.38  Reduction            : 0.09
% 2.83/1.38  Demodulation         : 0.06
% 2.83/1.38  BG Simplification    : 0.02
% 2.83/1.38  Subsumption          : 0.06
% 2.83/1.38  Abstraction          : 0.02
% 2.83/1.38  MUC search           : 0.00
% 2.83/1.38  Cooper               : 0.00
% 2.83/1.38  Total                : 0.65
% 2.83/1.38  Index Insertion      : 0.00
% 2.83/1.38  Index Deletion       : 0.00
% 2.83/1.38  Index Matching       : 0.00
% 2.83/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
