%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:20 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 133 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 396 expanded)
%              Number of equality atoms :   24 (  68 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_68,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_tarski(A_76,B_77),C_78)
      | ~ r2_hidden(B_77,C_78)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [A_79,C_80] :
      ( r1_tarski(k1_tarski(A_79),C_80)
      | ~ r2_hidden(A_79,C_80)
      | ~ r2_hidden(A_79,C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    ! [A_79,C_80] :
      ( k3_xboole_0(k1_tarski(A_79),C_80) = k1_tarski(A_79)
      | ~ r2_hidden(A_79,C_80) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_143,plain,(
    ! [A_3,C_78] :
      ( r1_tarski(k1_tarski(A_3),C_78)
      | ~ r2_hidden(A_3,C_78)
      | ~ r2_hidden(A_3,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_3'),B_68,'#skF_4') = k3_xboole_0(B_68,'#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_462,plain,(
    ! [A_114,B_115,C_116] :
      ( v4_pre_topc('#skF_1'(A_114,B_115,C_116),A_114)
      | ~ r1_tarski(C_116,B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3175,plain,(
    ! [A_316,B_317,B_318,C_319] :
      ( v4_pre_topc('#skF_1'(A_316,B_317,k9_subset_1(u1_struct_0(A_316),B_318,C_319)),A_316)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_316),B_318,C_319),B_317)
      | ~ v2_tex_2(B_317,A_316)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(u1_struct_0(A_316))) ) ),
    inference(resolution,[status(thm)],[c_12,c_462])).

tff(c_3208,plain,(
    ! [B_317,B_68] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_317,k3_xboole_0(B_68,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_68,'#skF_4'),B_317)
      | ~ v2_tex_2(B_317,'#skF_3')
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_3175])).

tff(c_3230,plain,(
    ! [B_317,B_68] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_317,k3_xboole_0(B_68,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_68,'#skF_4'),B_317)
      | ~ v2_tex_2(B_317,'#skF_3')
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_98,c_3208])).

tff(c_108,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1(k9_subset_1(A_71,B_72,C_73),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [B_68] :
      ( m1_subset_1(k3_xboole_0(B_68,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_108])).

tff(c_121,plain,(
    ! [B_68] : m1_subset_1(k3_xboole_0(B_68,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117])).

tff(c_1058,plain,(
    ! [A_167,B_168,C_169] :
      ( k9_subset_1(u1_struct_0(A_167),B_168,'#skF_1'(A_167,B_168,C_169)) = C_169
      | ~ r1_tarski(C_169,B_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v2_tex_2(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4354,plain,(
    ! [A_395,B_396,B_397,C_398] :
      ( k9_subset_1(u1_struct_0(A_395),B_396,'#skF_1'(A_395,B_396,k9_subset_1(u1_struct_0(A_395),B_397,C_398))) = k9_subset_1(u1_struct_0(A_395),B_397,C_398)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_395),B_397,C_398),B_396)
      | ~ v2_tex_2(B_396,A_395)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(u1_struct_0(A_395))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1058])).

tff(c_4429,plain,(
    ! [B_396,B_68] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_396,'#skF_1'('#skF_3',B_396,k3_xboole_0(B_68,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_68,'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_68,'#skF_4'),B_396)
      | ~ v2_tex_2(B_396,'#skF_3')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4354])).

tff(c_5707,plain,(
    ! [B_533,B_534] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_533,'#skF_1'('#skF_3',B_533,k3_xboole_0(B_534,'#skF_4'))) = k3_xboole_0(B_534,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(B_534,'#skF_4'),B_533)
      | ~ v2_tex_2(B_533,'#skF_3')
      | ~ m1_subset_1(B_533,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_98,c_98,c_4429])).

tff(c_946,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1('#skF_1'(A_154,B_155,C_156),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ r1_tarski(C_156,B_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ v2_tex_2(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [D_51] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_51) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_51,'#skF_3')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_956,plain,(
    ! [B_155,C_156] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_155,C_156)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_155,C_156),'#skF_3')
      | ~ r1_tarski(C_156,B_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_946,c_30])).

tff(c_962,plain,(
    ! [B_155,C_156] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_155,C_156)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_155,C_156),'#skF_3')
      | ~ r1_tarski(C_156,B_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_155,'#skF_3')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_956])).

tff(c_5719,plain,(
    ! [B_534] :
      ( k3_xboole_0(B_534,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_534,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_534,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_xboole_0(B_534,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_534,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5707,c_962])).

tff(c_5904,plain,(
    ! [B_548] :
      ( k3_xboole_0(B_548,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_548,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_548,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_38,c_36,c_121,c_5719])).

tff(c_5908,plain,(
    ! [B_68] :
      ( k3_xboole_0(B_68,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_68,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_3230,c_5904])).

tff(c_5920,plain,(
    ! [B_549] :
      ( k3_xboole_0(B_549,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_549,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5908])).

tff(c_5975,plain,(
    ! [A_554] :
      ( k3_xboole_0(k1_tarski(A_554),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_554),'#skF_4')
      | ~ r2_hidden(A_554,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_5920])).

tff(c_5981,plain,(
    ! [A_555] :
      ( k3_xboole_0(k1_tarski(A_555),'#skF_4') != k1_tarski('#skF_5')
      | ~ r2_hidden(A_555,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_5975])).

tff(c_5986,plain,(
    ! [A_556] :
      ( k1_tarski(A_556) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_556,'#skF_4')
      | ~ r2_hidden(A_556,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_5981])).

tff(c_5988,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_5986])).

tff(c_5992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.74  
% 7.43/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.74  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.43/2.74  
% 7.43/2.74  %Foreground sorts:
% 7.43/2.74  
% 7.43/2.74  
% 7.43/2.74  %Background operators:
% 7.43/2.74  
% 7.43/2.74  
% 7.43/2.74  %Foreground operators:
% 7.43/2.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.43/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.43/2.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.43/2.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.43/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.43/2.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.43/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.43/2.74  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.43/2.74  tff('#skF_3', type, '#skF_3': $i).
% 7.43/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.43/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.43/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.43/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.43/2.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.43/2.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.43/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.43/2.74  
% 7.43/2.75  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 7.43/2.75  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.43/2.75  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.43/2.75  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.43/2.75  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.43/2.75  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.43/2.75  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 7.43/2.75  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.43/2.75  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.43/2.75  tff(c_131, plain, (![A_76, B_77, C_78]: (r1_tarski(k2_tarski(A_76, B_77), C_78) | ~r2_hidden(B_77, C_78) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.43/2.75  tff(c_147, plain, (![A_79, C_80]: (r1_tarski(k1_tarski(A_79), C_80) | ~r2_hidden(A_79, C_80) | ~r2_hidden(A_79, C_80))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 7.43/2.75  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.43/2.75  tff(c_155, plain, (![A_79, C_80]: (k3_xboole_0(k1_tarski(A_79), C_80)=k1_tarski(A_79) | ~r2_hidden(A_79, C_80))), inference(resolution, [status(thm)], [c_147, c_2])).
% 7.43/2.75  tff(c_143, plain, (![A_3, C_78]: (r1_tarski(k1_tarski(A_3), C_78) | ~r2_hidden(A_3, C_78) | ~r2_hidden(A_3, C_78))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 7.43/2.75  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.43/2.75  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.43/2.75  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.43/2.75  tff(c_95, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.43/2.75  tff(c_98, plain, (![B_68]: (k9_subset_1(u1_struct_0('#skF_3'), B_68, '#skF_4')=k3_xboole_0(B_68, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_95])).
% 7.43/2.75  tff(c_12, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.43/2.75  tff(c_462, plain, (![A_114, B_115, C_116]: (v4_pre_topc('#skF_1'(A_114, B_115, C_116), A_114) | ~r1_tarski(C_116, B_115) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_114))) | ~v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.43/2.75  tff(c_3175, plain, (![A_316, B_317, B_318, C_319]: (v4_pre_topc('#skF_1'(A_316, B_317, k9_subset_1(u1_struct_0(A_316), B_318, C_319)), A_316) | ~r1_tarski(k9_subset_1(u1_struct_0(A_316), B_318, C_319), B_317) | ~v2_tex_2(B_317, A_316) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316) | ~m1_subset_1(C_319, k1_zfmisc_1(u1_struct_0(A_316))))), inference(resolution, [status(thm)], [c_12, c_462])).
% 7.43/2.75  tff(c_3208, plain, (![B_317, B_68]: (v4_pre_topc('#skF_1'('#skF_3', B_317, k3_xboole_0(B_68, '#skF_4')), '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_68, '#skF_4'), B_317) | ~v2_tex_2(B_317, '#skF_3') | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_3175])).
% 7.43/2.75  tff(c_3230, plain, (![B_317, B_68]: (v4_pre_topc('#skF_1'('#skF_3', B_317, k3_xboole_0(B_68, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_68, '#skF_4'), B_317) | ~v2_tex_2(B_317, '#skF_3') | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_98, c_3208])).
% 7.43/2.75  tff(c_108, plain, (![A_71, B_72, C_73]: (m1_subset_1(k9_subset_1(A_71, B_72, C_73), k1_zfmisc_1(A_71)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.43/2.75  tff(c_117, plain, (![B_68]: (m1_subset_1(k3_xboole_0(B_68, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_108])).
% 7.43/2.75  tff(c_121, plain, (![B_68]: (m1_subset_1(k3_xboole_0(B_68, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_117])).
% 7.43/2.75  tff(c_1058, plain, (![A_167, B_168, C_169]: (k9_subset_1(u1_struct_0(A_167), B_168, '#skF_1'(A_167, B_168, C_169))=C_169 | ~r1_tarski(C_169, B_168) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_167))) | ~v2_tex_2(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.43/2.75  tff(c_4354, plain, (![A_395, B_396, B_397, C_398]: (k9_subset_1(u1_struct_0(A_395), B_396, '#skF_1'(A_395, B_396, k9_subset_1(u1_struct_0(A_395), B_397, C_398)))=k9_subset_1(u1_struct_0(A_395), B_397, C_398) | ~r1_tarski(k9_subset_1(u1_struct_0(A_395), B_397, C_398), B_396) | ~v2_tex_2(B_396, A_395) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395) | ~m1_subset_1(C_398, k1_zfmisc_1(u1_struct_0(A_395))))), inference(resolution, [status(thm)], [c_12, c_1058])).
% 7.43/2.75  tff(c_4429, plain, (![B_396, B_68]: (k9_subset_1(u1_struct_0('#skF_3'), B_396, '#skF_1'('#skF_3', B_396, k3_xboole_0(B_68, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_68, '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_68, '#skF_4'), B_396) | ~v2_tex_2(B_396, '#skF_3') | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_4354])).
% 7.43/2.75  tff(c_5707, plain, (![B_533, B_534]: (k9_subset_1(u1_struct_0('#skF_3'), B_533, '#skF_1'('#skF_3', B_533, k3_xboole_0(B_534, '#skF_4')))=k3_xboole_0(B_534, '#skF_4') | ~r1_tarski(k3_xboole_0(B_534, '#skF_4'), B_533) | ~v2_tex_2(B_533, '#skF_3') | ~m1_subset_1(B_533, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_98, c_98, c_4429])).
% 7.43/2.75  tff(c_946, plain, (![A_154, B_155, C_156]: (m1_subset_1('#skF_1'(A_154, B_155, C_156), k1_zfmisc_1(u1_struct_0(A_154))) | ~r1_tarski(C_156, B_155) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_154))) | ~v2_tex_2(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.43/2.75  tff(c_30, plain, (![D_51]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_51)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_51, '#skF_3') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.43/2.75  tff(c_956, plain, (![B_155, C_156]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_155, C_156))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_155, C_156), '#skF_3') | ~r1_tarski(C_156, B_155) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_946, c_30])).
% 7.43/2.75  tff(c_962, plain, (![B_155, C_156]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_155, C_156))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_155, C_156), '#skF_3') | ~r1_tarski(C_156, B_155) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_155, '#skF_3') | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_956])).
% 7.43/2.75  tff(c_5719, plain, (![B_534]: (k3_xboole_0(B_534, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_534, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_534, '#skF_4'), '#skF_4') | ~m1_subset_1(k3_xboole_0(B_534, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k3_xboole_0(B_534, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_5707, c_962])).
% 7.43/2.75  tff(c_5904, plain, (![B_548]: (k3_xboole_0(B_548, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_548, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_548, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_38, c_36, c_121, c_5719])).
% 7.43/2.75  tff(c_5908, plain, (![B_68]: (k3_xboole_0(B_68, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_68, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_3230, c_5904])).
% 7.43/2.75  tff(c_5920, plain, (![B_549]: (k3_xboole_0(B_549, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_549, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_5908])).
% 7.43/2.75  tff(c_5975, plain, (![A_554]: (k3_xboole_0(k1_tarski(A_554), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_554), '#skF_4') | ~r2_hidden(A_554, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_5920])).
% 7.43/2.75  tff(c_5981, plain, (![A_555]: (k3_xboole_0(k1_tarski(A_555), '#skF_4')!=k1_tarski('#skF_5') | ~r2_hidden(A_555, '#skF_4'))), inference(resolution, [status(thm)], [c_143, c_5975])).
% 7.43/2.75  tff(c_5986, plain, (![A_556]: (k1_tarski(A_556)!=k1_tarski('#skF_5') | ~r2_hidden(A_556, '#skF_4') | ~r2_hidden(A_556, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_5981])).
% 7.43/2.75  tff(c_5988, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_5986])).
% 7.43/2.75  tff(c_5992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_5988])).
% 7.43/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.75  
% 7.43/2.75  Inference rules
% 7.43/2.75  ----------------------
% 7.43/2.75  #Ref     : 0
% 7.43/2.75  #Sup     : 1455
% 7.43/2.75  #Fact    : 0
% 7.43/2.75  #Define  : 0
% 7.43/2.75  #Split   : 2
% 7.43/2.75  #Chain   : 0
% 7.43/2.75  #Close   : 0
% 7.43/2.75  
% 7.43/2.75  Ordering : KBO
% 7.43/2.75  
% 7.43/2.75  Simplification rules
% 7.43/2.75  ----------------------
% 7.43/2.75  #Subsume      : 139
% 7.43/2.75  #Demod        : 550
% 7.43/2.75  #Tautology    : 99
% 7.43/2.75  #SimpNegUnit  : 0
% 7.43/2.75  #BackRed      : 4
% 7.43/2.75  
% 7.43/2.75  #Partial instantiations: 0
% 7.43/2.75  #Strategies tried      : 1
% 7.43/2.75  
% 7.43/2.75  Timing (in seconds)
% 7.43/2.75  ----------------------
% 7.43/2.76  Preprocessing        : 0.33
% 7.43/2.76  Parsing              : 0.18
% 7.43/2.76  CNF conversion       : 0.03
% 7.43/2.76  Main loop            : 1.58
% 7.43/2.76  Inferencing          : 0.51
% 7.43/2.76  Reduction            : 0.55
% 7.43/2.76  Demodulation         : 0.41
% 7.43/2.76  BG Simplification    : 0.07
% 7.43/2.76  Subsumption          : 0.34
% 7.43/2.76  Abstraction          : 0.09
% 7.43/2.76  MUC search           : 0.00
% 7.43/2.76  Cooper               : 0.00
% 7.43/2.76  Total                : 1.94
% 7.43/2.76  Index Insertion      : 0.00
% 7.43/2.76  Index Deletion       : 0.00
% 7.43/2.76  Index Matching       : 0.00
% 7.43/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
