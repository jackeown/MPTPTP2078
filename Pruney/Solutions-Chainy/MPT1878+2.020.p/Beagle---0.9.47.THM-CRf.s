%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.23s
% Verified   : 
% Statistics : Number of formulae       :   78 (  99 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 ( 245 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_22,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8),k1_zfmisc_1(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [A_47,C_48,B_49] :
      ( m1_subset_1(A_47,C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [A_52,A_53] :
      ( m1_subset_1(A_52,A_53)
      | ~ r2_hidden(A_52,'#skF_2'(A_53))
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_16,c_95])).

tff(c_113,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_53)),A_53)
      | v1_xboole_0(A_53)
      | v1_xboole_0('#skF_2'(A_53)) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_42,plain,(
    ! [A_30,B_32] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_18])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_575,plain,(
    ! [C_100,B_101,A_102] :
      ( C_100 = B_101
      | ~ r1_tarski(B_101,C_100)
      | ~ v2_tex_2(C_100,A_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_577,plain,(
    ! [A_6,A_102] :
      ( A_6 = '#skF_5'
      | ~ v2_tex_2(A_6,A_102)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_5',A_102)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_69,c_575])).

tff(c_581,plain,(
    ! [A_103,A_104] :
      ( A_103 = '#skF_5'
      | ~ v2_tex_2(A_103,A_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tex_2('#skF_5',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_577])).

tff(c_904,plain,(
    ! [A_129,B_130] :
      ( k6_domain_1(u1_struct_0(A_129),B_130) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_129),B_130),A_129)
      | ~ v3_tex_2('#skF_5',A_129)
      | ~ l1_pre_topc(A_129)
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | v1_xboole_0(u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_26,c_581])).

tff(c_917,plain,(
    ! [A_131,B_132] :
      ( k6_domain_1(u1_struct_0(A_131),B_132) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_131)
      | v1_xboole_0(u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_42,c_904])).

tff(c_1025,plain,(
    ! [A_139] :
      ( k6_domain_1(u1_struct_0(A_139),'#skF_1'('#skF_2'(u1_struct_0(A_139)))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139)
      | v1_xboole_0(u1_struct_0(A_139))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_139))) ) ),
    inference(resolution,[status(thm)],[c_113,c_917])).

tff(c_150,plain,(
    ! [A_60] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_60)),A_60)
      | v1_xboole_0(A_60)
      | v1_xboole_0('#skF_2'(A_60)) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( k6_domain_1(A_18,B_19) = k1_tarski(B_19)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_157,plain,(
    ! [A_60] :
      ( k6_domain_1(A_60,'#skF_1'('#skF_2'(A_60))) = k1_tarski('#skF_1'('#skF_2'(A_60)))
      | v1_xboole_0(A_60)
      | v1_xboole_0('#skF_2'(A_60)) ) ),
    inference(resolution,[status(thm)],[c_150,c_28])).

tff(c_3150,plain,(
    ! [A_225] :
      ( k1_tarski('#skF_1'('#skF_2'(u1_struct_0(A_225)))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_225))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_225)))
      | ~ v3_tex_2('#skF_5',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225)
      | v1_xboole_0(u1_struct_0(A_225))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_225))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_157])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3183,plain,(
    ! [A_225] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0(u1_struct_0(A_225))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_225)))
      | ~ v3_tex_2('#skF_5',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225)
      | v1_xboole_0(u1_struct_0(A_225))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_225))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3150,c_12])).

tff(c_3192,plain,(
    ! [A_226] :
      ( ~ v3_tex_2('#skF_5',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226)
      | v1_xboole_0(u1_struct_0(A_226))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_226))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3183])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_2'(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3201,plain,(
    ! [A_227] :
      ( ~ v3_tex_2('#skF_5',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227)
      | v1_xboole_0(u1_struct_0(A_227)) ) ),
    inference(resolution,[status(thm)],[c_3192,c_14])).

tff(c_24,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3210,plain,(
    ! [A_228] :
      ( ~ l1_struct_0(A_228)
      | ~ v3_tex_2('#skF_5',A_228)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_3201,c_24])).

tff(c_3216,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_3210])).

tff(c_3220,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3216])).

tff(c_3221,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3220])).

tff(c_3224,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3221])).

tff(c_3228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.20  
% 6.23/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.20  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 6.23/2.20  
% 6.23/2.20  %Foreground sorts:
% 6.23/2.20  
% 6.23/2.20  
% 6.23/2.20  %Background operators:
% 6.23/2.20  
% 6.23/2.20  
% 6.23/2.20  %Foreground operators:
% 6.23/2.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.23/2.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.23/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.23/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.23/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.23/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.23/2.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.23/2.20  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.23/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.20  tff('#skF_5', type, '#skF_5': $i).
% 6.23/2.20  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.23/2.20  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.23/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.23/2.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.23/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.23/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.23/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.23/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.23/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.23/2.20  
% 6.23/2.22  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 6.23/2.22  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.23/2.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.23/2.22  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 6.23/2.22  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.23/2.22  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.23/2.22  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.23/2.22  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.23/2.22  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.23/2.22  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.23/2.22  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 6.23/2.22  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.23/2.22  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.23/2.22  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.23/2.22  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.23/2.22  tff(c_22, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.23/2.22  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.23/2.22  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.23/2.22  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.23/2.22  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.23/2.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.23/2.22  tff(c_16, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), k1_zfmisc_1(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.23/2.22  tff(c_95, plain, (![A_47, C_48, B_49]: (m1_subset_1(A_47, C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.23/2.22  tff(c_108, plain, (![A_52, A_53]: (m1_subset_1(A_52, A_53) | ~r2_hidden(A_52, '#skF_2'(A_53)) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_16, c_95])).
% 6.23/2.22  tff(c_113, plain, (![A_53]: (m1_subset_1('#skF_1'('#skF_2'(A_53)), A_53) | v1_xboole_0(A_53) | v1_xboole_0('#skF_2'(A_53)))), inference(resolution, [status(thm)], [c_4, c_108])).
% 6.23/2.22  tff(c_42, plain, (![A_30, B_32]: (v2_tex_2(k6_domain_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.23/2.22  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.23/2.22  tff(c_58, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.23/2.22  tff(c_67, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_58])).
% 6.23/2.22  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.23/2.22  tff(c_77, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_18])).
% 6.23/2.22  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.23/2.22  tff(c_69, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_10])).
% 6.23/2.22  tff(c_575, plain, (![C_100, B_101, A_102]: (C_100=B_101 | ~r1_tarski(B_101, C_100) | ~v2_tex_2(C_100, A_102) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.23/2.22  tff(c_577, plain, (![A_6, A_102]: (A_6='#skF_5' | ~v2_tex_2(A_6, A_102) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2('#skF_5', A_102) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_69, c_575])).
% 6.23/2.22  tff(c_581, plain, (![A_103, A_104]: (A_103='#skF_5' | ~v2_tex_2(A_103, A_104) | ~m1_subset_1(A_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~v3_tex_2('#skF_5', A_104) | ~l1_pre_topc(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_577])).
% 6.23/2.22  tff(c_904, plain, (![A_129, B_130]: (k6_domain_1(u1_struct_0(A_129), B_130)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_129), B_130), A_129) | ~v3_tex_2('#skF_5', A_129) | ~l1_pre_topc(A_129) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | v1_xboole_0(u1_struct_0(A_129)))), inference(resolution, [status(thm)], [c_26, c_581])).
% 6.23/2.22  tff(c_917, plain, (![A_131, B_132]: (k6_domain_1(u1_struct_0(A_131), B_132)='#skF_5' | ~v3_tex_2('#skF_5', A_131) | v1_xboole_0(u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_42, c_904])).
% 6.23/2.22  tff(c_1025, plain, (![A_139]: (k6_domain_1(u1_struct_0(A_139), '#skF_1'('#skF_2'(u1_struct_0(A_139))))='#skF_5' | ~v3_tex_2('#skF_5', A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139) | v1_xboole_0(u1_struct_0(A_139)) | v1_xboole_0('#skF_2'(u1_struct_0(A_139))))), inference(resolution, [status(thm)], [c_113, c_917])).
% 6.23/2.22  tff(c_150, plain, (![A_60]: (m1_subset_1('#skF_1'('#skF_2'(A_60)), A_60) | v1_xboole_0(A_60) | v1_xboole_0('#skF_2'(A_60)))), inference(resolution, [status(thm)], [c_4, c_108])).
% 6.23/2.22  tff(c_28, plain, (![A_18, B_19]: (k6_domain_1(A_18, B_19)=k1_tarski(B_19) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.23/2.22  tff(c_157, plain, (![A_60]: (k6_domain_1(A_60, '#skF_1'('#skF_2'(A_60)))=k1_tarski('#skF_1'('#skF_2'(A_60))) | v1_xboole_0(A_60) | v1_xboole_0('#skF_2'(A_60)))), inference(resolution, [status(thm)], [c_150, c_28])).
% 6.23/2.22  tff(c_3150, plain, (![A_225]: (k1_tarski('#skF_1'('#skF_2'(u1_struct_0(A_225))))='#skF_5' | v1_xboole_0(u1_struct_0(A_225)) | v1_xboole_0('#skF_2'(u1_struct_0(A_225))) | ~v3_tex_2('#skF_5', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225) | v1_xboole_0(u1_struct_0(A_225)) | v1_xboole_0('#skF_2'(u1_struct_0(A_225))))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_157])).
% 6.23/2.22  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.23/2.22  tff(c_3183, plain, (![A_225]: (~v1_xboole_0('#skF_5') | v1_xboole_0(u1_struct_0(A_225)) | v1_xboole_0('#skF_2'(u1_struct_0(A_225))) | ~v3_tex_2('#skF_5', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225) | v1_xboole_0(u1_struct_0(A_225)) | v1_xboole_0('#skF_2'(u1_struct_0(A_225))))), inference(superposition, [status(thm), theory('equality')], [c_3150, c_12])).
% 6.23/2.22  tff(c_3192, plain, (![A_226]: (~v3_tex_2('#skF_5', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226) | v1_xboole_0(u1_struct_0(A_226)) | v1_xboole_0('#skF_2'(u1_struct_0(A_226))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3183])).
% 6.23/2.22  tff(c_14, plain, (![A_8]: (~v1_xboole_0('#skF_2'(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.23/2.22  tff(c_3201, plain, (![A_227]: (~v3_tex_2('#skF_5', A_227) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227) | v1_xboole_0(u1_struct_0(A_227)))), inference(resolution, [status(thm)], [c_3192, c_14])).
% 6.23/2.22  tff(c_24, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.23/2.22  tff(c_3210, plain, (![A_228]: (~l1_struct_0(A_228) | ~v3_tex_2('#skF_5', A_228) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_3201, c_24])).
% 6.23/2.22  tff(c_3216, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_3210])).
% 6.23/2.22  tff(c_3220, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3216])).
% 6.23/2.22  tff(c_3221, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_3220])).
% 6.23/2.22  tff(c_3224, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3221])).
% 6.23/2.22  tff(c_3228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3224])).
% 6.23/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.23/2.22  
% 6.23/2.22  Inference rules
% 6.23/2.22  ----------------------
% 6.23/2.22  #Ref     : 0
% 6.23/2.22  #Sup     : 838
% 6.23/2.22  #Fact    : 2
% 6.23/2.22  #Define  : 0
% 6.23/2.22  #Split   : 2
% 6.23/2.22  #Chain   : 0
% 6.23/2.22  #Close   : 0
% 6.23/2.22  
% 6.23/2.22  Ordering : KBO
% 6.23/2.22  
% 6.23/2.22  Simplification rules
% 6.23/2.22  ----------------------
% 6.23/2.22  #Subsume      : 77
% 6.23/2.22  #Demod        : 151
% 6.23/2.22  #Tautology    : 118
% 6.23/2.22  #SimpNegUnit  : 11
% 6.23/2.22  #BackRed      : 11
% 6.23/2.22  
% 6.23/2.22  #Partial instantiations: 0
% 6.23/2.22  #Strategies tried      : 1
% 6.23/2.22  
% 6.23/2.22  Timing (in seconds)
% 6.23/2.22  ----------------------
% 6.23/2.22  Preprocessing        : 0.31
% 6.23/2.22  Parsing              : 0.17
% 6.23/2.22  CNF conversion       : 0.02
% 6.23/2.22  Main loop            : 1.16
% 6.23/2.22  Inferencing          : 0.39
% 6.23/2.22  Reduction            : 0.33
% 6.23/2.22  Demodulation         : 0.22
% 6.23/2.22  BG Simplification    : 0.05
% 6.23/2.22  Subsumption          : 0.30
% 6.23/2.22  Abstraction          : 0.05
% 6.23/2.22  MUC search           : 0.00
% 6.23/2.22  Cooper               : 0.00
% 6.23/2.22  Total                : 1.50
% 6.23/2.22  Index Insertion      : 0.00
% 6.23/2.22  Index Deletion       : 0.00
% 6.23/2.22  Index Matching       : 0.00
% 6.23/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
