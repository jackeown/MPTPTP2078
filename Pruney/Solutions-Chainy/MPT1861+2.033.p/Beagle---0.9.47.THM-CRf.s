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
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 13.39s
% Output     : CNFRefutation 13.51s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 245 expanded)
%              Number of leaves         :   23 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 488 expanded)
%              Number of equality atoms :   22 (  70 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1297,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,B_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1308,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_1297])).

tff(c_1310,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1321,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1308,c_1310])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1354,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1361,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1354,c_4])).

tff(c_1322,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_1310])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1532,plain,(
    ! [A_110,B_111,C_112] :
      ( k9_subset_1(A_110,B_111,C_112) = k3_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1948,plain,(
    ! [B_134,B_135,A_136] :
      ( k9_subset_1(B_134,B_135,A_136) = k3_xboole_0(B_135,A_136)
      | ~ r1_tarski(A_136,B_134) ) ),
    inference(resolution,[status(thm)],[c_14,c_1532])).

tff(c_1974,plain,(
    ! [B_135] : k9_subset_1('#skF_3',B_135,'#skF_3') = k3_xboole_0(B_135,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1354,c_1948])).

tff(c_1561,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k9_subset_1(A_115,B_116,C_117),k1_zfmisc_1(A_115))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2011,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_tarski(k9_subset_1(A_140,B_141,C_142),A_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_1561,c_12])).

tff(c_2024,plain,(
    ! [B_135] :
      ( r1_tarski(k3_xboole_0(B_135,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_2011])).

tff(c_2180,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2024])).

tff(c_2183,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2180])).

tff(c_2187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_2183])).

tff(c_2189,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2024])).

tff(c_1981,plain,(
    ! [B_137] : k9_subset_1('#skF_3',B_137,'#skF_3') = k3_xboole_0(B_137,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1354,c_1948])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1987,plain,(
    ! [B_137] :
      ( m1_subset_1(k3_xboole_0(B_137,'#skF_3'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_6])).

tff(c_3288,plain,(
    ! [B_200] : m1_subset_1(k3_xboole_0(B_200,'#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2189,c_1987])).

tff(c_3301,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_3',B_2),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_3288])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_76,plain,(
    ! [A_36,B_37,C_38] :
      ( k9_subset_1(A_36,B_37,C_38) = k3_xboole_0(B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_2') = k3_xboole_0(B_37,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_213,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k9_subset_1(A_45,B_46,C_47),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [B_37] :
      ( m1_subset_1(k3_xboole_0(B_37,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_213])).

tff(c_269,plain,(
    ! [B_51] : m1_subset_1(k3_xboole_0(B_51,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_224])).

tff(c_278,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_2',B_2),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_269])).

tff(c_381,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_tex_2(C_57,A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ r1_tarski(C_57,B_59)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1214,plain,(
    ! [A_93,B_94,A_95] :
      ( v2_tex_2(k3_xboole_0(A_93,B_94),A_95)
      | ~ v2_tex_2(A_93,A_95)
      | ~ m1_subset_1(k3_xboole_0(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(A_93,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_2,c_381])).

tff(c_1238,plain,(
    ! [B_2] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_2),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_278,c_1214])).

tff(c_1275,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0('#skF_2',B_2),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_28,c_1238])).

tff(c_84,plain,(
    ! [B_37] : k9_subset_1(u1_struct_0('#skF_1'),B_37,'#skF_3') = k3_xboole_0(B_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_18,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_203])).

tff(c_1294,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_1540,plain,(
    ! [B_111] : k9_subset_1(u1_struct_0('#skF_1'),B_111,'#skF_3') = k3_xboole_0(B_111,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1532])).

tff(c_1572,plain,(
    ! [B_111] :
      ( m1_subset_1(k3_xboole_0(B_111,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_1561])).

tff(c_1578,plain,(
    ! [B_111] : m1_subset_1(k3_xboole_0(B_111,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1572])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( k9_subset_1(A_8,B_9,C_10) = k3_xboole_0(B_9,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2076,plain,(
    ! [A_144,B_145,B_146,C_147] :
      ( k9_subset_1(A_144,B_145,k9_subset_1(A_144,B_146,C_147)) = k3_xboole_0(B_145,k9_subset_1(A_144,B_146,C_147))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_1561,c_8])).

tff(c_2092,plain,(
    ! [B_145,B_146] : k9_subset_1(u1_struct_0('#skF_1'),B_145,k9_subset_1(u1_struct_0('#skF_1'),B_146,'#skF_3')) = k3_xboole_0(B_145,k9_subset_1(u1_struct_0('#skF_1'),B_146,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_2076])).

tff(c_2483,plain,(
    ! [B_164,B_165] : k9_subset_1(u1_struct_0('#skF_1'),B_164,k3_xboole_0(B_165,'#skF_3')) = k3_xboole_0(B_164,k3_xboole_0(B_165,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1540,c_2092])).

tff(c_2492,plain,(
    ! [B_164,B_165] :
      ( m1_subset_1(k3_xboole_0(B_164,k3_xboole_0(B_165,'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_xboole_0(B_165,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_6])).

tff(c_2752,plain,(
    ! [B_175,B_176] : m1_subset_1(k3_xboole_0(B_175,k3_xboole_0(B_176,'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_2492])).

tff(c_2772,plain,(
    ! [B_175,B_2] : m1_subset_1(k3_xboole_0(B_175,k3_xboole_0('#skF_3',B_2)),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_2752])).

tff(c_1980,plain,(
    ! [A_1,B_135,B_2] : k9_subset_1(A_1,B_135,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_135,k3_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_1948])).

tff(c_16,plain,(
    ! [C_21,A_15,B_19] :
      ( v2_tex_2(C_21,A_15)
      | ~ v2_tex_2(B_19,A_15)
      | ~ r1_tarski(C_21,B_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4976,plain,(
    ! [A_279,B_280,C_281,A_282] :
      ( v2_tex_2(k9_subset_1(A_279,B_280,C_281),A_282)
      | ~ v2_tex_2(A_279,A_282)
      | ~ m1_subset_1(k9_subset_1(A_279,B_280,C_281),k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(A_279,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(A_279)) ) ),
    inference(resolution,[status(thm)],[c_2011,c_16])).

tff(c_5000,plain,(
    ! [A_1,B_135,B_2,A_282] :
      ( v2_tex_2(k9_subset_1(A_1,B_135,k3_xboole_0(A_1,B_2)),A_282)
      | ~ v2_tex_2(A_1,A_282)
      | ~ m1_subset_1(k3_xboole_0(B_135,k3_xboole_0(A_1,B_2)),k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ m1_subset_1(k3_xboole_0(A_1,B_2),k1_zfmisc_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1980,c_4976])).

tff(c_30497,plain,(
    ! [B_895,A_896,B_897,A_898] :
      ( v2_tex_2(k3_xboole_0(B_895,k3_xboole_0(A_896,B_897)),A_898)
      | ~ v2_tex_2(A_896,A_898)
      | ~ m1_subset_1(k3_xboole_0(B_895,k3_xboole_0(A_896,B_897)),k1_zfmisc_1(u1_struct_0(A_898)))
      | ~ m1_subset_1(A_896,k1_zfmisc_1(u1_struct_0(A_898)))
      | ~ l1_pre_topc(A_898)
      | ~ m1_subset_1(k3_xboole_0(A_896,B_897),k1_zfmisc_1(A_896)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1980,c_5000])).

tff(c_30590,plain,(
    ! [B_175,B_2] :
      ( v2_tex_2(k3_xboole_0(B_175,k3_xboole_0('#skF_3',B_2)),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(k3_xboole_0('#skF_3',B_2),k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2772,c_30497])).

tff(c_30746,plain,(
    ! [B_899,B_900] : v2_tex_2(k3_xboole_0(B_899,k3_xboole_0('#skF_3',B_900)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_26,c_22,c_1294,c_30590])).

tff(c_30772,plain,(
    ! [B_899] : v2_tex_2(k3_xboole_0(B_899,'#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_30746])).

tff(c_1542,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_18])).

tff(c_30786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30772,c_1542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.39/6.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.50  
% 13.39/6.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.50  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 13.39/6.50  
% 13.39/6.50  %Foreground sorts:
% 13.39/6.50  
% 13.39/6.50  
% 13.39/6.50  %Background operators:
% 13.39/6.50  
% 13.39/6.50  
% 13.39/6.50  %Foreground operators:
% 13.39/6.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.39/6.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.39/6.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.39/6.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.39/6.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 13.39/6.50  tff('#skF_2', type, '#skF_2': $i).
% 13.39/6.50  tff('#skF_3', type, '#skF_3': $i).
% 13.39/6.50  tff('#skF_1', type, '#skF_1': $i).
% 13.39/6.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.39/6.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.39/6.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.39/6.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.39/6.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.39/6.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 13.39/6.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.39/6.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.39/6.50  
% 13.51/6.52  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 13.51/6.52  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.51/6.52  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.51/6.52  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.51/6.52  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 13.51/6.52  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 13.51/6.52  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 13.51/6.52  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.51/6.52  tff(c_1297, plain, (![A_98, B_99]: (r1_tarski(A_98, B_99) | ~m1_subset_1(A_98, k1_zfmisc_1(B_99)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.51/6.52  tff(c_1308, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1297])).
% 13.51/6.52  tff(c_1310, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.51/6.52  tff(c_1321, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_1308, c_1310])).
% 13.51/6.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.51/6.52  tff(c_1354, plain, (r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1321, c_2])).
% 13.51/6.52  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.51/6.52  tff(c_1361, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1354, c_4])).
% 13.51/6.52  tff(c_1322, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_1310])).
% 13.51/6.52  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.51/6.52  tff(c_1532, plain, (![A_110, B_111, C_112]: (k9_subset_1(A_110, B_111, C_112)=k3_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.51/6.52  tff(c_1948, plain, (![B_134, B_135, A_136]: (k9_subset_1(B_134, B_135, A_136)=k3_xboole_0(B_135, A_136) | ~r1_tarski(A_136, B_134))), inference(resolution, [status(thm)], [c_14, c_1532])).
% 13.51/6.52  tff(c_1974, plain, (![B_135]: (k9_subset_1('#skF_3', B_135, '#skF_3')=k3_xboole_0(B_135, '#skF_3'))), inference(resolution, [status(thm)], [c_1354, c_1948])).
% 13.51/6.52  tff(c_1561, plain, (![A_115, B_116, C_117]: (m1_subset_1(k9_subset_1(A_115, B_116, C_117), k1_zfmisc_1(A_115)) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.51/6.52  tff(c_12, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.51/6.52  tff(c_2011, plain, (![A_140, B_141, C_142]: (r1_tarski(k9_subset_1(A_140, B_141, C_142), A_140) | ~m1_subset_1(C_142, k1_zfmisc_1(A_140)))), inference(resolution, [status(thm)], [c_1561, c_12])).
% 13.51/6.52  tff(c_2024, plain, (![B_135]: (r1_tarski(k3_xboole_0(B_135, '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1974, c_2011])).
% 13.51/6.52  tff(c_2180, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2024])).
% 13.51/6.52  tff(c_2183, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_2180])).
% 13.51/6.52  tff(c_2187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1354, c_2183])).
% 13.51/6.52  tff(c_2189, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2024])).
% 13.51/6.52  tff(c_1981, plain, (![B_137]: (k9_subset_1('#skF_3', B_137, '#skF_3')=k3_xboole_0(B_137, '#skF_3'))), inference(resolution, [status(thm)], [c_1354, c_1948])).
% 13.51/6.52  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.51/6.52  tff(c_1987, plain, (![B_137]: (m1_subset_1(k3_xboole_0(B_137, '#skF_3'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1981, c_6])).
% 13.51/6.52  tff(c_3288, plain, (![B_200]: (m1_subset_1(k3_xboole_0(B_200, '#skF_3'), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2189, c_1987])).
% 13.51/6.52  tff(c_3301, plain, (![B_2]: (m1_subset_1(k3_xboole_0('#skF_3', B_2), k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_3288])).
% 13.51/6.52  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.51/6.52  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.51/6.52  tff(c_20, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.51/6.52  tff(c_28, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 13.51/6.52  tff(c_52, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.51/6.52  tff(c_64, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_52])).
% 13.51/6.52  tff(c_76, plain, (![A_36, B_37, C_38]: (k9_subset_1(A_36, B_37, C_38)=k3_xboole_0(B_37, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.51/6.52  tff(c_85, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_2')=k3_xboole_0(B_37, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_76])).
% 13.51/6.52  tff(c_213, plain, (![A_45, B_46, C_47]: (m1_subset_1(k9_subset_1(A_45, B_46, C_47), k1_zfmisc_1(A_45)) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.51/6.52  tff(c_224, plain, (![B_37]: (m1_subset_1(k3_xboole_0(B_37, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_85, c_213])).
% 13.51/6.52  tff(c_269, plain, (![B_51]: (m1_subset_1(k3_xboole_0(B_51, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_224])).
% 13.51/6.52  tff(c_278, plain, (![B_2]: (m1_subset_1(k3_xboole_0('#skF_2', B_2), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_64, c_269])).
% 13.51/6.52  tff(c_381, plain, (![C_57, A_58, B_59]: (v2_tex_2(C_57, A_58) | ~v2_tex_2(B_59, A_58) | ~r1_tarski(C_57, B_59) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.51/6.52  tff(c_1214, plain, (![A_93, B_94, A_95]: (v2_tex_2(k3_xboole_0(A_93, B_94), A_95) | ~v2_tex_2(A_93, A_95) | ~m1_subset_1(k3_xboole_0(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(A_93, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_2, c_381])).
% 13.51/6.52  tff(c_1238, plain, (![B_2]: (v2_tex_2(k3_xboole_0('#skF_2', B_2), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_278, c_1214])).
% 13.51/6.52  tff(c_1275, plain, (![B_2]: (v2_tex_2(k3_xboole_0('#skF_2', B_2), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_28, c_1238])).
% 13.51/6.52  tff(c_84, plain, (![B_37]: (k9_subset_1(u1_struct_0('#skF_1'), B_37, '#skF_3')=k3_xboole_0(B_37, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_76])).
% 13.51/6.52  tff(c_18, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.51/6.52  tff(c_203, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_18])).
% 13.51/6.52  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1275, c_203])).
% 13.51/6.52  tff(c_1294, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 13.51/6.52  tff(c_1540, plain, (![B_111]: (k9_subset_1(u1_struct_0('#skF_1'), B_111, '#skF_3')=k3_xboole_0(B_111, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1532])).
% 13.51/6.52  tff(c_1572, plain, (![B_111]: (m1_subset_1(k3_xboole_0(B_111, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_1561])).
% 13.51/6.52  tff(c_1578, plain, (![B_111]: (m1_subset_1(k3_xboole_0(B_111, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1572])).
% 13.51/6.52  tff(c_8, plain, (![A_8, B_9, C_10]: (k9_subset_1(A_8, B_9, C_10)=k3_xboole_0(B_9, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.51/6.52  tff(c_2076, plain, (![A_144, B_145, B_146, C_147]: (k9_subset_1(A_144, B_145, k9_subset_1(A_144, B_146, C_147))=k3_xboole_0(B_145, k9_subset_1(A_144, B_146, C_147)) | ~m1_subset_1(C_147, k1_zfmisc_1(A_144)))), inference(resolution, [status(thm)], [c_1561, c_8])).
% 13.51/6.52  tff(c_2092, plain, (![B_145, B_146]: (k9_subset_1(u1_struct_0('#skF_1'), B_145, k9_subset_1(u1_struct_0('#skF_1'), B_146, '#skF_3'))=k3_xboole_0(B_145, k9_subset_1(u1_struct_0('#skF_1'), B_146, '#skF_3')))), inference(resolution, [status(thm)], [c_22, c_2076])).
% 13.51/6.52  tff(c_2483, plain, (![B_164, B_165]: (k9_subset_1(u1_struct_0('#skF_1'), B_164, k3_xboole_0(B_165, '#skF_3'))=k3_xboole_0(B_164, k3_xboole_0(B_165, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1540, c_2092])).
% 13.51/6.52  tff(c_2492, plain, (![B_164, B_165]: (m1_subset_1(k3_xboole_0(B_164, k3_xboole_0(B_165, '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0(B_165, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2483, c_6])).
% 13.51/6.52  tff(c_2752, plain, (![B_175, B_176]: (m1_subset_1(k3_xboole_0(B_175, k3_xboole_0(B_176, '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_2492])).
% 13.51/6.52  tff(c_2772, plain, (![B_175, B_2]: (m1_subset_1(k3_xboole_0(B_175, k3_xboole_0('#skF_3', B_2)), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_2752])).
% 13.51/6.52  tff(c_1980, plain, (![A_1, B_135, B_2]: (k9_subset_1(A_1, B_135, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_135, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_1948])).
% 13.51/6.52  tff(c_16, plain, (![C_21, A_15, B_19]: (v2_tex_2(C_21, A_15) | ~v2_tex_2(B_19, A_15) | ~r1_tarski(C_21, B_19) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.51/6.52  tff(c_4976, plain, (![A_279, B_280, C_281, A_282]: (v2_tex_2(k9_subset_1(A_279, B_280, C_281), A_282) | ~v2_tex_2(A_279, A_282) | ~m1_subset_1(k9_subset_1(A_279, B_280, C_281), k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(A_279, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~m1_subset_1(C_281, k1_zfmisc_1(A_279)))), inference(resolution, [status(thm)], [c_2011, c_16])).
% 13.51/6.52  tff(c_5000, plain, (![A_1, B_135, B_2, A_282]: (v2_tex_2(k9_subset_1(A_1, B_135, k3_xboole_0(A_1, B_2)), A_282) | ~v2_tex_2(A_1, A_282) | ~m1_subset_1(k3_xboole_0(B_135, k3_xboole_0(A_1, B_2)), k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~m1_subset_1(k3_xboole_0(A_1, B_2), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1980, c_4976])).
% 13.51/6.52  tff(c_30497, plain, (![B_895, A_896, B_897, A_898]: (v2_tex_2(k3_xboole_0(B_895, k3_xboole_0(A_896, B_897)), A_898) | ~v2_tex_2(A_896, A_898) | ~m1_subset_1(k3_xboole_0(B_895, k3_xboole_0(A_896, B_897)), k1_zfmisc_1(u1_struct_0(A_898))) | ~m1_subset_1(A_896, k1_zfmisc_1(u1_struct_0(A_898))) | ~l1_pre_topc(A_898) | ~m1_subset_1(k3_xboole_0(A_896, B_897), k1_zfmisc_1(A_896)))), inference(demodulation, [status(thm), theory('equality')], [c_1980, c_5000])).
% 13.51/6.52  tff(c_30590, plain, (![B_175, B_2]: (v2_tex_2(k3_xboole_0(B_175, k3_xboole_0('#skF_3', B_2)), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k3_xboole_0('#skF_3', B_2), k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2772, c_30497])).
% 13.51/6.52  tff(c_30746, plain, (![B_899, B_900]: (v2_tex_2(k3_xboole_0(B_899, k3_xboole_0('#skF_3', B_900)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_26, c_22, c_1294, c_30590])).
% 13.51/6.52  tff(c_30772, plain, (![B_899]: (v2_tex_2(k3_xboole_0(B_899, '#skF_3'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_30746])).
% 13.51/6.52  tff(c_1542, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_18])).
% 13.51/6.52  tff(c_30786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30772, c_1542])).
% 13.51/6.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.51/6.52  
% 13.51/6.52  Inference rules
% 13.51/6.52  ----------------------
% 13.51/6.52  #Ref     : 0
% 13.51/6.52  #Sup     : 7043
% 13.51/6.52  #Fact    : 0
% 13.51/6.52  #Define  : 0
% 13.51/6.52  #Split   : 6
% 13.51/6.52  #Chain   : 0
% 13.51/6.52  #Close   : 0
% 13.51/6.52  
% 13.51/6.52  Ordering : KBO
% 13.51/6.52  
% 13.51/6.52  Simplification rules
% 13.51/6.52  ----------------------
% 13.51/6.52  #Subsume      : 134
% 13.51/6.52  #Demod        : 5896
% 13.51/6.52  #Tautology    : 3822
% 13.51/6.52  #SimpNegUnit  : 10
% 13.51/6.52  #BackRed      : 5
% 13.51/6.52  
% 13.51/6.52  #Partial instantiations: 0
% 13.51/6.52  #Strategies tried      : 1
% 13.51/6.52  
% 13.51/6.52  Timing (in seconds)
% 13.51/6.52  ----------------------
% 13.51/6.53  Preprocessing        : 0.30
% 13.51/6.53  Parsing              : 0.17
% 13.51/6.53  CNF conversion       : 0.02
% 13.51/6.53  Main loop            : 5.44
% 13.51/6.53  Inferencing          : 1.08
% 13.51/6.53  Reduction            : 2.97
% 13.51/6.53  Demodulation         : 2.61
% 13.51/6.53  BG Simplification    : 0.13
% 13.51/6.53  Subsumption          : 1.03
% 13.51/6.53  Abstraction          : 0.22
% 13.51/6.53  MUC search           : 0.00
% 13.51/6.53  Cooper               : 0.00
% 13.51/6.53  Total                : 5.79
% 13.51/6.53  Index Insertion      : 0.00
% 13.51/6.53  Index Deletion       : 0.00
% 13.51/6.53  Index Matching       : 0.00
% 13.51/6.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
