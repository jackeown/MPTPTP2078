%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:25 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 310 expanded)
%              Number of leaves         :   32 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 ( 859 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_101,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    ! [A_23] :
      ( v1_xboole_0('#skF_2'(A_23))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_2'(A_23),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_933,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_1'(A_175,B_176,C_177),B_176)
      | r1_tarski(B_176,C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [B_16,A_65,A_15] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_65,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_968,plain,(
    ! [B_181,B_182,C_183,A_184] :
      ( ~ v1_xboole_0(B_181)
      | ~ r1_tarski(B_182,B_181)
      | r1_tarski(B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_933,c_98])).

tff(c_990,plain,(
    ! [B_185,C_186,A_187] :
      ( ~ v1_xboole_0(B_185)
      | r1_tarski(B_185,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(A_187))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_6,c_968])).

tff(c_1007,plain,(
    ! [B_188] :
      ( ~ v1_xboole_0(B_188)
      | r1_tarski(B_188,'#skF_6')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_990])).

tff(c_1019,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_5'))
    | r1_tarski('#skF_2'('#skF_5'),'#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1007])).

tff(c_1033,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_5'))
    | r1_tarski('#skF_2'('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1019])).

tff(c_1075,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_1078,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1075])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1078])).

tff(c_1083,plain,(
    r1_tarski('#skF_2'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1095,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1083,c_2])).

tff(c_1129,plain,(
    ~ r1_tarski('#skF_6','#skF_2'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1095])).

tff(c_81,plain,(
    ! [A_61] :
      ( m1_subset_1('#skF_2'(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_61] :
      ( r1_tarski('#skF_2'(A_61),u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_81,c_18])).

tff(c_46,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1189,plain,(
    ! [B_196,A_197,B_198] :
      ( ~ v1_xboole_0(B_196)
      | r1_tarski(B_196,A_197)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(B_198))
      | ~ r1_tarski(A_197,B_198) ) ),
    inference(resolution,[status(thm)],[c_20,c_990])).

tff(c_1202,plain,(
    ! [A_197] :
      ( ~ v1_xboole_0('#skF_6')
      | r1_tarski('#skF_6',A_197)
      | ~ r1_tarski(A_197,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1189])).

tff(c_1211,plain,(
    ! [A_199] :
      ( r1_tarski('#skF_6',A_199)
      | ~ r1_tarski(A_199,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1202])).

tff(c_1223,plain,
    ( r1_tarski('#skF_6','#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_1211])).

tff(c_1241,plain,(
    r1_tarski('#skF_6','#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1223])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1129,c_1241])).

tff(c_1244,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1095])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1328,plain,(
    ! [B_204,A_205,B_206] :
      ( ~ v1_xboole_0(B_204)
      | r1_tarski(B_204,A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(B_206))
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(resolution,[status(thm)],[c_20,c_990])).

tff(c_1405,plain,(
    ! [A_211,A_212,B_213] :
      ( ~ v1_xboole_0(A_211)
      | r1_tarski(A_211,A_212)
      | ~ r1_tarski(A_212,B_213)
      | ~ r1_tarski(A_211,B_213) ) ),
    inference(resolution,[status(thm)],[c_20,c_1328])).

tff(c_1433,plain,(
    ! [A_214,A_215,B_216] :
      ( ~ v1_xboole_0(A_214)
      | r1_tarski(A_214,k3_xboole_0(A_215,B_216))
      | ~ r1_tarski(A_214,A_215) ) ),
    inference(resolution,[status(thm)],[c_8,c_1405])).

tff(c_67,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_1443,plain,(
    ! [A_215,B_216] :
      ( k3_xboole_0(A_215,B_216) = A_215
      | ~ v1_xboole_0(A_215)
      | ~ r1_tarski(A_215,A_215) ) ),
    inference(resolution,[status(thm)],[c_1433,c_75])).

tff(c_1453,plain,(
    ! [A_217,B_218] :
      ( k3_xboole_0(A_217,B_218) = A_217
      | ~ v1_xboole_0(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1443])).

tff(c_1459,plain,(
    ! [B_218] : k3_xboole_0('#skF_6',B_218) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_1453])).

tff(c_162,plain,(
    ! [A_84,B_85] :
      ( r1_tarski('#skF_4'(A_84,B_85),B_85)
      | v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_169,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_174,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_169])).

tff(c_175,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_174])).

tff(c_213,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_1'(A_97,B_98,C_99),B_98)
      | r1_tarski(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_293,plain,(
    ! [B_111,B_112,C_113,A_114] :
      ( ~ v1_xboole_0(B_111)
      | ~ r1_tarski(B_112,B_111)
      | r1_tarski(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_213,c_98])).

tff(c_317,plain,(
    ! [B_115,C_116,A_117] :
      ( ~ v1_xboole_0(B_115)
      | r1_tarski(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_6,c_293])).

tff(c_654,plain,(
    ! [B_136,A_137,B_138] :
      ( ~ v1_xboole_0(B_136)
      | r1_tarski(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(B_138))
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_20,c_317])).

tff(c_721,plain,(
    ! [A_143,A_144,B_145] :
      ( ~ v1_xboole_0(A_143)
      | r1_tarski(A_143,A_144)
      | ~ r1_tarski(A_144,B_145)
      | ~ r1_tarski(A_143,B_145) ) ),
    inference(resolution,[status(thm)],[c_20,c_654])).

tff(c_772,plain,(
    ! [A_149] :
      ( ~ v1_xboole_0(A_149)
      | r1_tarski(A_149,'#skF_4'('#skF_5','#skF_6'))
      | ~ r1_tarski(A_149,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_175,c_721])).

tff(c_181,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_175,c_2])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_6','#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_779,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_772,c_182])).

tff(c_789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46,c_779])).

tff(c_790,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_123,plain,(
    ! [B_77,A_78] :
      ( v3_pre_topc(B_77,A_78)
      | ~ v1_xboole_0(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_133,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_138,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_133])).

tff(c_104,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(A_73,B_74,C_75) = k3_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [B_74] : k9_subset_1(u1_struct_0('#skF_5'),B_74,'#skF_6') = k3_xboole_0(B_74,'#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_1302,plain,(
    ! [A_200,B_201,D_202] :
      ( k9_subset_1(u1_struct_0(A_200),B_201,D_202) != '#skF_4'(A_200,B_201)
      | ~ v3_pre_topc(D_202,A_200)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0(A_200)))
      | v2_tex_2(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1312,plain,(
    ! [B_74] :
      ( k3_xboole_0(B_74,'#skF_6') != '#skF_4'('#skF_5',B_74)
      | ~ v3_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_tex_2(B_74,'#skF_5')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1302])).

tff(c_2320,plain,(
    ! [B_276] :
      ( k3_xboole_0(B_276,'#skF_6') != '#skF_4'('#skF_5',B_276)
      | v2_tex_2(B_276,'#skF_5')
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_138,c_1312])).

tff(c_2336,plain,
    ( k3_xboole_0('#skF_2'('#skF_5'),'#skF_6') != '#skF_4'('#skF_5','#skF_2'('#skF_5'))
    | v2_tex_2('#skF_2'('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_2320])).

tff(c_2353,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1244,c_1459,c_790,c_1244,c_1244,c_2336])).

tff(c_2355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.85  
% 4.57/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.85  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.57/1.85  
% 4.57/1.85  %Foreground sorts:
% 4.57/1.85  
% 4.57/1.85  
% 4.57/1.85  %Background operators:
% 4.57/1.85  
% 4.57/1.85  
% 4.57/1.85  %Foreground operators:
% 4.57/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.57/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.57/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.57/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.57/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.57/1.85  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.57/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.57/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.57/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.57/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.57/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.57/1.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.57/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.85  
% 4.57/1.87  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 4.57/1.87  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 4.57/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.57/1.87  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 4.57/1.87  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.57/1.87  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.57/1.87  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.57/1.87  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 4.57/1.87  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 4.57/1.87  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.57/1.87  tff(c_42, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.57/1.87  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.57/1.87  tff(c_26, plain, (![A_23]: (v1_xboole_0('#skF_2'(A_23)) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.87  tff(c_28, plain, (![A_23]: (m1_subset_1('#skF_2'(A_23), k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.87  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.57/1.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.87  tff(c_933, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_1'(A_175, B_176, C_177), B_176) | r1_tarski(B_176, C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.87  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.87  tff(c_90, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.87  tff(c_98, plain, (![B_16, A_65, A_15]: (~v1_xboole_0(B_16) | ~r2_hidden(A_65, A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_90])).
% 4.57/1.87  tff(c_968, plain, (![B_181, B_182, C_183, A_184]: (~v1_xboole_0(B_181) | ~r1_tarski(B_182, B_181) | r1_tarski(B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_933, c_98])).
% 4.57/1.87  tff(c_990, plain, (![B_185, C_186, A_187]: (~v1_xboole_0(B_185) | r1_tarski(B_185, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(A_187)) | ~m1_subset_1(B_185, k1_zfmisc_1(A_187)))), inference(resolution, [status(thm)], [c_6, c_968])).
% 4.57/1.87  tff(c_1007, plain, (![B_188]: (~v1_xboole_0(B_188) | r1_tarski(B_188, '#skF_6') | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_44, c_990])).
% 4.57/1.87  tff(c_1019, plain, (~v1_xboole_0('#skF_2'('#skF_5')) | r1_tarski('#skF_2'('#skF_5'), '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1007])).
% 4.57/1.87  tff(c_1033, plain, (~v1_xboole_0('#skF_2'('#skF_5')) | r1_tarski('#skF_2'('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1019])).
% 4.57/1.87  tff(c_1075, plain, (~v1_xboole_0('#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_1033])).
% 4.57/1.87  tff(c_1078, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1075])).
% 4.57/1.87  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1078])).
% 4.57/1.87  tff(c_1083, plain, (r1_tarski('#skF_2'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_1033])).
% 4.57/1.87  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.87  tff(c_1095, plain, ('#skF_2'('#skF_5')='#skF_6' | ~r1_tarski('#skF_6', '#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_1083, c_2])).
% 4.57/1.87  tff(c_1129, plain, (~r1_tarski('#skF_6', '#skF_2'('#skF_5'))), inference(splitLeft, [status(thm)], [c_1095])).
% 4.57/1.87  tff(c_81, plain, (![A_61]: (m1_subset_1('#skF_2'(A_61), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.87  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.87  tff(c_85, plain, (![A_61]: (r1_tarski('#skF_2'(A_61), u1_struct_0(A_61)) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_81, c_18])).
% 4.57/1.87  tff(c_46, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.57/1.87  tff(c_1189, plain, (![B_196, A_197, B_198]: (~v1_xboole_0(B_196) | r1_tarski(B_196, A_197) | ~m1_subset_1(B_196, k1_zfmisc_1(B_198)) | ~r1_tarski(A_197, B_198))), inference(resolution, [status(thm)], [c_20, c_990])).
% 4.57/1.87  tff(c_1202, plain, (![A_197]: (~v1_xboole_0('#skF_6') | r1_tarski('#skF_6', A_197) | ~r1_tarski(A_197, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_44, c_1189])).
% 4.57/1.87  tff(c_1211, plain, (![A_199]: (r1_tarski('#skF_6', A_199) | ~r1_tarski(A_199, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1202])).
% 4.57/1.87  tff(c_1223, plain, (r1_tarski('#skF_6', '#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_85, c_1211])).
% 4.57/1.87  tff(c_1241, plain, (r1_tarski('#skF_6', '#skF_2'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1223])).
% 4.57/1.87  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1129, c_1241])).
% 4.57/1.87  tff(c_1244, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1095])).
% 4.57/1.87  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.57/1.87  tff(c_1328, plain, (![B_204, A_205, B_206]: (~v1_xboole_0(B_204) | r1_tarski(B_204, A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(B_206)) | ~r1_tarski(A_205, B_206))), inference(resolution, [status(thm)], [c_20, c_990])).
% 4.57/1.87  tff(c_1405, plain, (![A_211, A_212, B_213]: (~v1_xboole_0(A_211) | r1_tarski(A_211, A_212) | ~r1_tarski(A_212, B_213) | ~r1_tarski(A_211, B_213))), inference(resolution, [status(thm)], [c_20, c_1328])).
% 4.57/1.87  tff(c_1433, plain, (![A_214, A_215, B_216]: (~v1_xboole_0(A_214) | r1_tarski(A_214, k3_xboole_0(A_215, B_216)) | ~r1_tarski(A_214, A_215))), inference(resolution, [status(thm)], [c_8, c_1405])).
% 4.57/1.87  tff(c_67, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.87  tff(c_75, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_67])).
% 4.57/1.87  tff(c_1443, plain, (![A_215, B_216]: (k3_xboole_0(A_215, B_216)=A_215 | ~v1_xboole_0(A_215) | ~r1_tarski(A_215, A_215))), inference(resolution, [status(thm)], [c_1433, c_75])).
% 4.57/1.87  tff(c_1453, plain, (![A_217, B_218]: (k3_xboole_0(A_217, B_218)=A_217 | ~v1_xboole_0(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1443])).
% 4.57/1.87  tff(c_1459, plain, (![B_218]: (k3_xboole_0('#skF_6', B_218)='#skF_6')), inference(resolution, [status(thm)], [c_46, c_1453])).
% 4.57/1.87  tff(c_162, plain, (![A_84, B_85]: (r1_tarski('#skF_4'(A_84, B_85), B_85) | v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.57/1.87  tff(c_169, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_162])).
% 4.57/1.87  tff(c_174, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_169])).
% 4.57/1.87  tff(c_175, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_174])).
% 4.57/1.87  tff(c_213, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_1'(A_97, B_98, C_99), B_98) | r1_tarski(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.87  tff(c_293, plain, (![B_111, B_112, C_113, A_114]: (~v1_xboole_0(B_111) | ~r1_tarski(B_112, B_111) | r1_tarski(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_114)))), inference(resolution, [status(thm)], [c_213, c_98])).
% 4.57/1.87  tff(c_317, plain, (![B_115, C_116, A_117]: (~v1_xboole_0(B_115) | r1_tarski(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_6, c_293])).
% 4.57/1.87  tff(c_654, plain, (![B_136, A_137, B_138]: (~v1_xboole_0(B_136) | r1_tarski(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(B_138)) | ~r1_tarski(A_137, B_138))), inference(resolution, [status(thm)], [c_20, c_317])).
% 4.57/1.87  tff(c_721, plain, (![A_143, A_144, B_145]: (~v1_xboole_0(A_143) | r1_tarski(A_143, A_144) | ~r1_tarski(A_144, B_145) | ~r1_tarski(A_143, B_145))), inference(resolution, [status(thm)], [c_20, c_654])).
% 4.57/1.87  tff(c_772, plain, (![A_149]: (~v1_xboole_0(A_149) | r1_tarski(A_149, '#skF_4'('#skF_5', '#skF_6')) | ~r1_tarski(A_149, '#skF_6'))), inference(resolution, [status(thm)], [c_175, c_721])).
% 4.57/1.87  tff(c_181, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', '#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_175, c_2])).
% 4.57/1.87  tff(c_182, plain, (~r1_tarski('#skF_6', '#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_181])).
% 4.57/1.87  tff(c_779, plain, (~v1_xboole_0('#skF_6') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_772, c_182])).
% 4.57/1.87  tff(c_789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_46, c_779])).
% 4.57/1.87  tff(c_790, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_181])).
% 4.57/1.87  tff(c_50, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.57/1.87  tff(c_123, plain, (![B_77, A_78]: (v3_pre_topc(B_77, A_78) | ~v1_xboole_0(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.57/1.87  tff(c_133, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_123])).
% 4.57/1.87  tff(c_138, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_133])).
% 4.57/1.87  tff(c_104, plain, (![A_73, B_74, C_75]: (k9_subset_1(A_73, B_74, C_75)=k3_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.57/1.87  tff(c_113, plain, (![B_74]: (k9_subset_1(u1_struct_0('#skF_5'), B_74, '#skF_6')=k3_xboole_0(B_74, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_104])).
% 4.57/1.87  tff(c_1302, plain, (![A_200, B_201, D_202]: (k9_subset_1(u1_struct_0(A_200), B_201, D_202)!='#skF_4'(A_200, B_201) | ~v3_pre_topc(D_202, A_200) | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0(A_200))) | v2_tex_2(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.57/1.87  tff(c_1312, plain, (![B_74]: (k3_xboole_0(B_74, '#skF_6')!='#skF_4'('#skF_5', B_74) | ~v3_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_tex_2(B_74, '#skF_5') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1302])).
% 4.57/1.87  tff(c_2320, plain, (![B_276]: (k3_xboole_0(B_276, '#skF_6')!='#skF_4'('#skF_5', B_276) | v2_tex_2(B_276, '#skF_5') | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_138, c_1312])).
% 4.57/1.87  tff(c_2336, plain, (k3_xboole_0('#skF_2'('#skF_5'), '#skF_6')!='#skF_4'('#skF_5', '#skF_2'('#skF_5')) | v2_tex_2('#skF_2'('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_28, c_2320])).
% 4.57/1.87  tff(c_2353, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1244, c_1459, c_790, c_1244, c_1244, c_2336])).
% 4.57/1.87  tff(c_2355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2353])).
% 4.57/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.87  
% 4.57/1.87  Inference rules
% 4.57/1.87  ----------------------
% 4.57/1.87  #Ref     : 0
% 4.57/1.87  #Sup     : 509
% 4.57/1.87  #Fact    : 0
% 4.57/1.87  #Define  : 0
% 4.57/1.87  #Split   : 8
% 4.57/1.87  #Chain   : 0
% 4.57/1.87  #Close   : 0
% 4.57/1.87  
% 4.57/1.87  Ordering : KBO
% 4.57/1.87  
% 4.57/1.87  Simplification rules
% 4.57/1.87  ----------------------
% 4.57/1.87  #Subsume      : 64
% 4.57/1.87  #Demod        : 329
% 4.57/1.87  #Tautology    : 138
% 4.57/1.87  #SimpNegUnit  : 21
% 4.57/1.87  #BackRed      : 5
% 4.57/1.87  
% 4.57/1.87  #Partial instantiations: 0
% 4.57/1.87  #Strategies tried      : 1
% 4.57/1.87  
% 4.57/1.87  Timing (in seconds)
% 4.57/1.87  ----------------------
% 4.57/1.87  Preprocessing        : 0.35
% 4.57/1.87  Parsing              : 0.18
% 4.57/1.87  CNF conversion       : 0.03
% 4.57/1.87  Main loop            : 0.68
% 4.57/1.87  Inferencing          : 0.23
% 4.57/1.87  Reduction            : 0.22
% 4.57/1.87  Demodulation         : 0.14
% 4.57/1.87  BG Simplification    : 0.03
% 4.57/1.87  Subsumption          : 0.15
% 4.57/1.87  Abstraction          : 0.04
% 4.57/1.87  MUC search           : 0.00
% 4.57/1.87  Cooper               : 0.00
% 4.57/1.87  Total                : 1.07
% 4.57/1.87  Index Insertion      : 0.00
% 4.57/1.87  Index Deletion       : 0.00
% 4.57/1.87  Index Matching       : 0.00
% 4.57/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
