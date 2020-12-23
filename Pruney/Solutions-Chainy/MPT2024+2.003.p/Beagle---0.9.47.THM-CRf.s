%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 536 expanded)
%              Number of leaves         :   43 ( 216 expanded)
%              Depth                    :   18
%              Number of atoms          :  348 (1880 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [A_90,B_91] :
      ( k2_xboole_0(A_90,B_91) = B_91
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    ! [B_6] : k2_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_379,plain,(
    ! [A_120,C_121,B_122] :
      ( r2_hidden(A_120,C_121)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_120,B_122),C_121),C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_387,plain,(
    ! [A_120,B_122] :
      ( r2_hidden(A_120,k2_tarski(A_120,B_122))
      | ~ r1_tarski(k2_tarski(A_120,B_122),k2_tarski(A_120,B_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_379])).

tff(c_395,plain,(
    ! [A_123,B_124] : r2_hidden(A_123,k2_tarski(A_123,B_124)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_387])).

tff(c_411,plain,(
    ! [A_128] : r2_hidden(A_128,k1_tarski(A_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_395])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_418,plain,(
    ! [A_128] : m1_subset_1(A_128,k1_tarski(A_128)) ),
    inference(resolution,[status(thm)],[c_411,c_38])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_653,plain,(
    ! [C_167,A_168,B_169] :
      ( m1_connsp_2(C_167,A_168,B_169)
      | ~ m1_subset_1(C_167,u1_struct_0(k9_yellow_6(A_168,B_169)))
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_664,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_653])).

tff(c_672,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_664])).

tff(c_673,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_672])).

tff(c_44,plain,(
    ! [C_41,A_38,B_39] :
      ( m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_connsp_2(C_41,A_38,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_679,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_673,c_44])).

tff(c_682,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_679])).

tff(c_683,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_682])).

tff(c_711,plain,(
    ! [C_170,B_171,A_172] :
      ( r2_hidden(C_170,B_171)
      | ~ m1_connsp_2(B_171,A_172,C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(A_172))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_715,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_673,c_711])).

tff(c_722,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_683,c_62,c_715])).

tff(c_723,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_722])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_407,plain,(
    ! [A_125,B_126] : ~ v1_xboole_0(k2_tarski(A_125,B_126)) ),
    inference(resolution,[status(thm)],[c_395,c_2])).

tff(c_409,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_407])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [A_106,B_107] :
      ( k2_xboole_0(k1_tarski(A_106),B_107) = B_107
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tarski(A_106),B_107)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_16])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_620,plain,(
    ! [A_162,C_163,B_164] :
      ( r1_tarski(k1_tarski(A_162),C_163)
      | ~ r1_tarski(B_164,C_163)
      | ~ r2_hidden(A_162,B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_12])).

tff(c_879,plain,(
    ! [A_186,B_187,A_188] :
      ( r1_tarski(k1_tarski(A_186),B_187)
      | ~ r2_hidden(A_186,k1_tarski(A_188))
      | ~ r2_hidden(A_188,B_187) ) ),
    inference(resolution,[status(thm)],[c_268,c_620])).

tff(c_884,plain,(
    ! [B_23,B_187,A_188] :
      ( r1_tarski(k1_tarski(B_23),B_187)
      | ~ r2_hidden(A_188,B_187)
      | ~ m1_subset_1(B_23,k1_tarski(A_188))
      | v1_xboole_0(k1_tarski(A_188)) ) ),
    inference(resolution,[status(thm)],[c_28,c_879])).

tff(c_1271,plain,(
    ! [B_210,B_211,A_212] :
      ( r1_tarski(k1_tarski(B_210),B_211)
      | ~ r2_hidden(A_212,B_211)
      | ~ m1_subset_1(B_210,k1_tarski(A_212)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_884])).

tff(c_1299,plain,(
    ! [B_213] :
      ( r1_tarski(k1_tarski(B_213),'#skF_4')
      | ~ m1_subset_1(B_213,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_723,c_1271])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1439,plain,(
    ! [B_221] :
      ( k2_xboole_0(k1_tarski(B_221),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_221,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1299,c_14])).

tff(c_1457,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_418,c_1439])).

tff(c_205,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,C_99)
      | ~ r1_tarski(k2_xboole_0(A_98,B_100),C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_98,B_100,B_13] : r1_tarski(A_98,k2_xboole_0(k2_xboole_0(A_98,B_100),B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_205])).

tff(c_1565,plain,(
    ! [B_223] : r1_tarski(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',B_223)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_217])).

tff(c_3176,plain,(
    ! [B_300] : k2_xboole_0(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',B_300)) = k2_xboole_0('#skF_4',B_300) ),
    inference(resolution,[status(thm)],[c_1565,c_14])).

tff(c_390,plain,(
    ! [A_14,C_121] :
      ( r2_hidden(A_14,C_121)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_14),C_121),C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_379])).

tff(c_3197,plain,(
    ! [B_300] :
      ( r2_hidden('#skF_3',k2_xboole_0('#skF_4',B_300))
      | ~ r1_tarski(k2_xboole_0('#skF_4',B_300),k2_xboole_0('#skF_4',B_300)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3176,c_390])).

tff(c_3253,plain,(
    ! [B_300] : r2_hidden('#skF_3',k2_xboole_0('#skF_4',B_300)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3197])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_667,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_653])).

tff(c_676,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_667])).

tff(c_677,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_676])).

tff(c_685,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_677,c_44])).

tff(c_688,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_685])).

tff(c_689,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_688])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] :
      ( k4_subset_1(A_27,B_28,C_29) = k2_xboole_0(B_28,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_809,plain,(
    ! [B_184] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_184,'#skF_5') = k2_xboole_0(B_184,'#skF_5')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_689,c_36])).

tff(c_830,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_683,c_809])).

tff(c_34,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k4_subset_1(A_24,B_25,C_26),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_848,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_34])).

tff(c_852,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_689,c_848])).

tff(c_1321,plain,(
    ! [C_215,A_216,B_217] :
      ( r2_hidden(C_215,u1_struct_0(k9_yellow_6(A_216,B_217)))
      | ~ v3_pre_topc(C_215,A_216)
      | ~ r2_hidden(B_217,C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3160,plain,(
    ! [C_297,A_298,B_299] :
      ( m1_subset_1(C_297,u1_struct_0(k9_yellow_6(A_298,B_299)))
      | ~ v3_pre_topc(C_297,A_298)
      | ~ r2_hidden(B_299,C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m1_subset_1(B_299,u1_struct_0(A_298))
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_1321,c_38])).

tff(c_56,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3166,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3160,c_56])).

tff(c_3173,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_852,c_3166])).

tff(c_3174,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3173])).

tff(c_3299,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3253,c_3174])).

tff(c_93,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,A_85)
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_195,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_754,plain,(
    ! [C_174,A_175,B_176] :
      ( v3_pre_topc(C_174,A_175)
      | ~ r2_hidden(C_174,u1_struct_0(k9_yellow_6(A_175,B_176)))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3513,plain,(
    ! [B_313,A_314,B_315] :
      ( v3_pre_topc(B_313,A_314)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ m1_subset_1(B_315,u1_struct_0(A_314))
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314)
      | ~ m1_subset_1(B_313,u1_struct_0(k9_yellow_6(A_314,B_315)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_314,B_315))) ) ),
    inference(resolution,[status(thm)],[c_28,c_754])).

tff(c_3531,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_60,c_3513])).

tff(c_3541,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_683,c_3531])).

tff(c_3542,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_68,c_3541])).

tff(c_3534,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_3513])).

tff(c_3545,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_689,c_3534])).

tff(c_3546,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_68,c_3545])).

tff(c_1126,plain,(
    ! [B_201,C_202,A_203] :
      ( v3_pre_topc(k2_xboole_0(B_201,C_202),A_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ v3_pre_topc(C_202,A_203)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ v3_pre_topc(B_201,A_203)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1135,plain,(
    ! [B_201] :
      ( v3_pre_topc(k2_xboole_0(B_201,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_201,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_689,c_1126])).

tff(c_1156,plain,(
    ! [B_201] :
      ( v3_pre_topc(k2_xboole_0(B_201,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_201,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1135])).

tff(c_4307,plain,(
    ! [B_344] :
      ( v3_pre_topc(k2_xboole_0(B_344,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_344,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_344,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3546,c_1156])).

tff(c_4335,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_683,c_4307])).

tff(c_4362,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_4335])).

tff(c_4364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3299,c_4362])).

tff(c_4366,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_93])).

tff(c_4368,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4366,c_108])).

tff(c_4944,plain,(
    ! [C_425,A_426,B_427] :
      ( m1_connsp_2(C_425,A_426,B_427)
      | ~ m1_subset_1(C_425,u1_struct_0(k9_yellow_6(A_426,B_427)))
      | ~ m1_subset_1(B_427,u1_struct_0(A_426))
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_4958,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_4944])).

tff(c_4967,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_4958])).

tff(c_4968,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4967])).

tff(c_4976,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4968,c_44])).

tff(c_4979,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_4976])).

tff(c_4980,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4979])).

tff(c_5008,plain,(
    ! [C_429,B_430,A_431] :
      ( r2_hidden(C_429,B_430)
      | ~ m1_connsp_2(B_430,A_431,C_429)
      | ~ m1_subset_1(C_429,u1_struct_0(A_431))
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0(A_431)))
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5010,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4968,c_5008])).

tff(c_5015,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4980,c_62,c_5010])).

tff(c_5016,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5015])).

tff(c_5026,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5016,c_2])).

tff(c_5031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4368,c_5026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.21  
% 5.93/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.22  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.93/2.22  
% 5.93/2.22  %Foreground sorts:
% 5.93/2.22  
% 5.93/2.22  
% 5.93/2.22  %Background operators:
% 5.93/2.22  
% 5.93/2.22  
% 5.93/2.22  %Foreground operators:
% 5.93/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.93/2.22  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.93/2.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.93/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.93/2.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.93/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.93/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.93/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.93/2.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.93/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.93/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.22  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.93/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.93/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.93/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.93/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.93/2.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.93/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.22  
% 6.34/2.24  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.34/2.24  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.34/2.24  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.34/2.24  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.34/2.24  tff(f_88, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.34/2.24  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 6.34/2.24  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 6.34/2.24  tff(f_122, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 6.34/2.24  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 6.34/2.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.34/2.24  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.34/2.24  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 6.34/2.24  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.34/2.24  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.34/2.24  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.34/2.24  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 6.34/2.24  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 6.34/2.24  tff(f_108, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 6.34/2.24  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.34/2.24  tff(c_18, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.24  tff(c_148, plain, (![A_90, B_91]: (k2_xboole_0(A_90, B_91)=B_91 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.24  tff(c_160, plain, (![B_6]: (k2_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_148])).
% 6.34/2.24  tff(c_379, plain, (![A_120, C_121, B_122]: (r2_hidden(A_120, C_121) | ~r1_tarski(k2_xboole_0(k2_tarski(A_120, B_122), C_121), C_121))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.34/2.24  tff(c_387, plain, (![A_120, B_122]: (r2_hidden(A_120, k2_tarski(A_120, B_122)) | ~r1_tarski(k2_tarski(A_120, B_122), k2_tarski(A_120, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_379])).
% 6.34/2.24  tff(c_395, plain, (![A_123, B_124]: (r2_hidden(A_123, k2_tarski(A_123, B_124)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_387])).
% 6.34/2.24  tff(c_411, plain, (![A_128]: (r2_hidden(A_128, k1_tarski(A_128)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_395])).
% 6.34/2.24  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(A_30, B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.34/2.24  tff(c_418, plain, (![A_128]: (m1_subset_1(A_128, k1_tarski(A_128)))), inference(resolution, [status(thm)], [c_411, c_38])).
% 6.34/2.24  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_62, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_60, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_653, plain, (![C_167, A_168, B_169]: (m1_connsp_2(C_167, A_168, B_169) | ~m1_subset_1(C_167, u1_struct_0(k9_yellow_6(A_168, B_169))) | ~m1_subset_1(B_169, u1_struct_0(A_168)) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.34/2.24  tff(c_664, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_653])).
% 6.34/2.24  tff(c_672, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_664])).
% 6.34/2.24  tff(c_673, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_672])).
% 6.34/2.24  tff(c_44, plain, (![C_41, A_38, B_39]: (m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_connsp_2(C_41, A_38, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.34/2.24  tff(c_679, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_673, c_44])).
% 6.34/2.24  tff(c_682, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_679])).
% 6.34/2.24  tff(c_683, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_682])).
% 6.34/2.24  tff(c_711, plain, (![C_170, B_171, A_172]: (r2_hidden(C_170, B_171) | ~m1_connsp_2(B_171, A_172, C_170) | ~m1_subset_1(C_170, u1_struct_0(A_172)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.34/2.24  tff(c_715, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_673, c_711])).
% 6.34/2.24  tff(c_722, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_683, c_62, c_715])).
% 6.34/2.24  tff(c_723, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_722])).
% 6.34/2.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.24  tff(c_407, plain, (![A_125, B_126]: (~v1_xboole_0(k2_tarski(A_125, B_126)))), inference(resolution, [status(thm)], [c_395, c_2])).
% 6.34/2.24  tff(c_409, plain, (![A_14]: (~v1_xboole_0(k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_407])).
% 6.34/2.24  tff(c_28, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.34/2.24  tff(c_252, plain, (![A_106, B_107]: (k2_xboole_0(k1_tarski(A_106), B_107)=B_107 | ~r2_hidden(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.34/2.24  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.34/2.24  tff(c_268, plain, (![A_106, B_107]: (r1_tarski(k1_tarski(A_106), B_107) | ~r2_hidden(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_252, c_16])).
% 6.34/2.24  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.24  tff(c_620, plain, (![A_162, C_163, B_164]: (r1_tarski(k1_tarski(A_162), C_163) | ~r1_tarski(B_164, C_163) | ~r2_hidden(A_162, B_164))), inference(superposition, [status(thm), theory('equality')], [c_252, c_12])).
% 6.34/2.24  tff(c_879, plain, (![A_186, B_187, A_188]: (r1_tarski(k1_tarski(A_186), B_187) | ~r2_hidden(A_186, k1_tarski(A_188)) | ~r2_hidden(A_188, B_187))), inference(resolution, [status(thm)], [c_268, c_620])).
% 6.34/2.24  tff(c_884, plain, (![B_23, B_187, A_188]: (r1_tarski(k1_tarski(B_23), B_187) | ~r2_hidden(A_188, B_187) | ~m1_subset_1(B_23, k1_tarski(A_188)) | v1_xboole_0(k1_tarski(A_188)))), inference(resolution, [status(thm)], [c_28, c_879])).
% 6.34/2.24  tff(c_1271, plain, (![B_210, B_211, A_212]: (r1_tarski(k1_tarski(B_210), B_211) | ~r2_hidden(A_212, B_211) | ~m1_subset_1(B_210, k1_tarski(A_212)))), inference(negUnitSimplification, [status(thm)], [c_409, c_884])).
% 6.34/2.24  tff(c_1299, plain, (![B_213]: (r1_tarski(k1_tarski(B_213), '#skF_4') | ~m1_subset_1(B_213, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_723, c_1271])).
% 6.34/2.24  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.24  tff(c_1439, plain, (![B_221]: (k2_xboole_0(k1_tarski(B_221), '#skF_4')='#skF_4' | ~m1_subset_1(B_221, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_1299, c_14])).
% 6.34/2.24  tff(c_1457, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_418, c_1439])).
% 6.34/2.24  tff(c_205, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, C_99) | ~r1_tarski(k2_xboole_0(A_98, B_100), C_99))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.24  tff(c_217, plain, (![A_98, B_100, B_13]: (r1_tarski(A_98, k2_xboole_0(k2_xboole_0(A_98, B_100), B_13)))), inference(resolution, [status(thm)], [c_16, c_205])).
% 6.34/2.24  tff(c_1565, plain, (![B_223]: (r1_tarski(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', B_223)))), inference(superposition, [status(thm), theory('equality')], [c_1457, c_217])).
% 6.34/2.24  tff(c_3176, plain, (![B_300]: (k2_xboole_0(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', B_300))=k2_xboole_0('#skF_4', B_300))), inference(resolution, [status(thm)], [c_1565, c_14])).
% 6.34/2.24  tff(c_390, plain, (![A_14, C_121]: (r2_hidden(A_14, C_121) | ~r1_tarski(k2_xboole_0(k1_tarski(A_14), C_121), C_121))), inference(superposition, [status(thm), theory('equality')], [c_18, c_379])).
% 6.34/2.24  tff(c_3197, plain, (![B_300]: (r2_hidden('#skF_3', k2_xboole_0('#skF_4', B_300)) | ~r1_tarski(k2_xboole_0('#skF_4', B_300), k2_xboole_0('#skF_4', B_300)))), inference(superposition, [status(thm), theory('equality')], [c_3176, c_390])).
% 6.34/2.24  tff(c_3253, plain, (![B_300]: (r2_hidden('#skF_3', k2_xboole_0('#skF_4', B_300)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3197])).
% 6.34/2.24  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_667, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_653])).
% 6.34/2.24  tff(c_676, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_667])).
% 6.34/2.24  tff(c_677, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_676])).
% 6.34/2.24  tff(c_685, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_677, c_44])).
% 6.34/2.24  tff(c_688, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_685])).
% 6.34/2.24  tff(c_689, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_688])).
% 6.34/2.24  tff(c_36, plain, (![A_27, B_28, C_29]: (k4_subset_1(A_27, B_28, C_29)=k2_xboole_0(B_28, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.34/2.24  tff(c_809, plain, (![B_184]: (k4_subset_1(u1_struct_0('#skF_2'), B_184, '#skF_5')=k2_xboole_0(B_184, '#skF_5') | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_689, c_36])).
% 6.34/2.24  tff(c_830, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_683, c_809])).
% 6.34/2.24  tff(c_34, plain, (![A_24, B_25, C_26]: (m1_subset_1(k4_subset_1(A_24, B_25, C_26), k1_zfmisc_1(A_24)) | ~m1_subset_1(C_26, k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.34/2.24  tff(c_848, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_830, c_34])).
% 6.34/2.24  tff(c_852, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_689, c_848])).
% 6.34/2.24  tff(c_1321, plain, (![C_215, A_216, B_217]: (r2_hidden(C_215, u1_struct_0(k9_yellow_6(A_216, B_217))) | ~v3_pre_topc(C_215, A_216) | ~r2_hidden(B_217, C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.34/2.24  tff(c_3160, plain, (![C_297, A_298, B_299]: (m1_subset_1(C_297, u1_struct_0(k9_yellow_6(A_298, B_299))) | ~v3_pre_topc(C_297, A_298) | ~r2_hidden(B_299, C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(u1_struct_0(A_298))) | ~m1_subset_1(B_299, u1_struct_0(A_298)) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(resolution, [status(thm)], [c_1321, c_38])).
% 6.34/2.24  tff(c_56, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.34/2.24  tff(c_3166, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3160, c_56])).
% 6.34/2.24  tff(c_3173, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_852, c_3166])).
% 6.34/2.24  tff(c_3174, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_3173])).
% 6.34/2.24  tff(c_3299, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3253, c_3174])).
% 6.34/2.24  tff(c_93, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, A_85) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.34/2.24  tff(c_107, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_60, c_93])).
% 6.34/2.24  tff(c_195, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_107])).
% 6.34/2.24  tff(c_754, plain, (![C_174, A_175, B_176]: (v3_pre_topc(C_174, A_175) | ~r2_hidden(C_174, u1_struct_0(k9_yellow_6(A_175, B_176))) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.34/2.24  tff(c_3513, plain, (![B_313, A_314, B_315]: (v3_pre_topc(B_313, A_314) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_314))) | ~m1_subset_1(B_315, u1_struct_0(A_314)) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314) | ~m1_subset_1(B_313, u1_struct_0(k9_yellow_6(A_314, B_315))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_314, B_315))))), inference(resolution, [status(thm)], [c_28, c_754])).
% 6.34/2.24  tff(c_3531, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_60, c_3513])).
% 6.34/2.24  tff(c_3541, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_683, c_3531])).
% 6.34/2.24  tff(c_3542, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_195, c_68, c_3541])).
% 6.34/2.24  tff(c_3534, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_58, c_3513])).
% 6.34/2.24  tff(c_3545, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_689, c_3534])).
% 6.34/2.24  tff(c_3546, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_195, c_68, c_3545])).
% 6.34/2.24  tff(c_1126, plain, (![B_201, C_202, A_203]: (v3_pre_topc(k2_xboole_0(B_201, C_202), A_203) | ~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~v3_pre_topc(C_202, A_203) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_203))) | ~v3_pre_topc(B_201, A_203) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.34/2.24  tff(c_1135, plain, (![B_201]: (v3_pre_topc(k2_xboole_0(B_201, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_201, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_689, c_1126])).
% 6.34/2.24  tff(c_1156, plain, (![B_201]: (v3_pre_topc(k2_xboole_0(B_201, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_201, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1135])).
% 6.34/2.24  tff(c_4307, plain, (![B_344]: (v3_pre_topc(k2_xboole_0(B_344, '#skF_5'), '#skF_2') | ~m1_subset_1(B_344, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_344, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3546, c_1156])).
% 6.34/2.24  tff(c_4335, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_683, c_4307])).
% 6.34/2.24  tff(c_4362, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3542, c_4335])).
% 6.34/2.24  tff(c_4364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3299, c_4362])).
% 6.34/2.24  tff(c_4366, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_107])).
% 6.34/2.24  tff(c_108, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_58, c_93])).
% 6.34/2.24  tff(c_4368, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4366, c_108])).
% 6.34/2.24  tff(c_4944, plain, (![C_425, A_426, B_427]: (m1_connsp_2(C_425, A_426, B_427) | ~m1_subset_1(C_425, u1_struct_0(k9_yellow_6(A_426, B_427))) | ~m1_subset_1(B_427, u1_struct_0(A_426)) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_173])).
% 6.34/2.24  tff(c_4958, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_4944])).
% 6.34/2.24  tff(c_4967, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_4958])).
% 6.34/2.24  tff(c_4968, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_4967])).
% 6.34/2.24  tff(c_4976, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4968, c_44])).
% 6.34/2.24  tff(c_4979, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_4976])).
% 6.34/2.24  tff(c_4980, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_4979])).
% 6.34/2.24  tff(c_5008, plain, (![C_429, B_430, A_431]: (r2_hidden(C_429, B_430) | ~m1_connsp_2(B_430, A_431, C_429) | ~m1_subset_1(C_429, u1_struct_0(A_431)) | ~m1_subset_1(B_430, k1_zfmisc_1(u1_struct_0(A_431))) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.34/2.24  tff(c_5010, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4968, c_5008])).
% 6.34/2.24  tff(c_5015, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4980, c_62, c_5010])).
% 6.34/2.24  tff(c_5016, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_5015])).
% 6.34/2.24  tff(c_5026, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5016, c_2])).
% 6.34/2.24  tff(c_5031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4368, c_5026])).
% 6.34/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.24  
% 6.34/2.24  Inference rules
% 6.34/2.24  ----------------------
% 6.34/2.24  #Ref     : 0
% 6.34/2.24  #Sup     : 1149
% 6.34/2.24  #Fact    : 0
% 6.34/2.24  #Define  : 0
% 6.34/2.24  #Split   : 5
% 6.34/2.24  #Chain   : 0
% 6.34/2.24  #Close   : 0
% 6.34/2.24  
% 6.34/2.24  Ordering : KBO
% 6.34/2.24  
% 6.34/2.24  Simplification rules
% 6.34/2.24  ----------------------
% 6.34/2.24  #Subsume      : 208
% 6.34/2.24  #Demod        : 539
% 6.34/2.24  #Tautology    : 390
% 6.34/2.24  #SimpNegUnit  : 43
% 6.34/2.24  #BackRed      : 2
% 6.34/2.24  
% 6.34/2.24  #Partial instantiations: 0
% 6.34/2.24  #Strategies tried      : 1
% 6.34/2.24  
% 6.34/2.24  Timing (in seconds)
% 6.34/2.24  ----------------------
% 6.34/2.25  Preprocessing        : 0.37
% 6.34/2.25  Parsing              : 0.20
% 6.34/2.25  CNF conversion       : 0.03
% 6.34/2.25  Main loop            : 1.06
% 6.34/2.25  Inferencing          : 0.37
% 6.34/2.25  Reduction            : 0.38
% 6.34/2.25  Demodulation         : 0.27
% 6.34/2.25  BG Simplification    : 0.04
% 6.34/2.25  Subsumption          : 0.20
% 6.34/2.25  Abstraction          : 0.05
% 6.34/2.25  MUC search           : 0.00
% 6.34/2.25  Cooper               : 0.00
% 6.34/2.25  Total                : 1.48
% 6.34/2.25  Index Insertion      : 0.00
% 6.34/2.25  Index Deletion       : 0.00
% 6.34/2.25  Index Matching       : 0.00
% 6.34/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
