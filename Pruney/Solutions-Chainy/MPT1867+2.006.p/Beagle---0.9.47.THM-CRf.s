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
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 177 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 347 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    ! [A_23] :
      ( v3_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_66,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_18])).

tff(c_26,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_103,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_290,plain,(
    ! [A_93,B_94] :
      ( r1_tarski('#skF_2'(A_93,B_94),B_94)
      | v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_298,plain,(
    ! [B_94] :
      ( r1_tarski('#skF_2'('#skF_3',B_94),B_94)
      | v2_tex_2(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_290])).

tff(c_359,plain,(
    ! [B_100] :
      ( r1_tarski('#skF_2'('#skF_3',B_100),B_100)
      | v2_tex_2(B_100,'#skF_3')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_298])).

tff(c_368,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_359])).

tff(c_376,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_368])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ r1_tarski(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_6])).

tff(c_381,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_376,c_92])).

tff(c_136,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(A_73,B_74,C_75) = k3_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_76,B_77] : k9_subset_1(A_76,B_77,A_76) = k3_xboole_0(B_77,A_76) ),
    inference(resolution,[status(thm)],[c_53,c_136])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [B_77,A_76] :
      ( m1_subset_1(k3_xboole_0(B_77,A_76),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(A_76,k1_zfmisc_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_14])).

tff(c_160,plain,(
    ! [B_78,A_79] : m1_subset_1(k3_xboole_0(B_78,A_79),k1_zfmisc_1(A_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_152])).

tff(c_20,plain,(
    ! [B_17,A_15] :
      ( v1_xboole_0(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_171,plain,(
    ! [B_80,A_81] :
      ( v1_xboole_0(k3_xboole_0(B_80,A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_160,c_20])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_76,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4])).

tff(c_190,plain,(
    ! [B_85,A_86] :
      ( k3_xboole_0(B_85,A_86) = '#skF_4'
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_171,c_76])).

tff(c_196,plain,(
    ! [B_85] : k3_xboole_0(B_85,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_190])).

tff(c_144,plain,(
    ! [A_14,B_74] : k9_subset_1(A_14,B_74,'#skF_4') = k3_xboole_0(B_74,'#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_136])).

tff(c_236,plain,(
    ! [A_14,B_74] : k9_subset_1(A_14,B_74,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_144])).

tff(c_176,plain,(
    ! [A_82,C_83,B_84] :
      ( k9_subset_1(A_82,C_83,B_84) = k9_subset_1(A_82,B_84,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [A_14,B_84] : k9_subset_1(A_14,B_84,'#skF_4') = k9_subset_1(A_14,'#skF_4',B_84) ),
    inference(resolution,[status(thm)],[c_77,c_176])).

tff(c_312,plain,(
    ! [A_14,B_84] : k9_subset_1(A_14,'#skF_4',B_84) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_187])).

tff(c_1177,plain,(
    ! [A_151,B_152,D_153] :
      ( k9_subset_1(u1_struct_0(A_151),B_152,D_153) != '#skF_2'(A_151,B_152)
      | ~ v3_pre_topc(D_153,A_151)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1194,plain,(
    ! [B_152,D_153] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_152,D_153) != '#skF_2'('#skF_3',B_152)
      | ~ v3_pre_topc(D_153,'#skF_3')
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_152,'#skF_3')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_1177])).

tff(c_1208,plain,(
    ! [B_154,D_155] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_154,D_155) != '#skF_2'('#skF_3',B_154)
      | ~ v3_pre_topc(D_155,'#skF_3')
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_103,c_103,c_1194])).

tff(c_1214,plain,(
    ! [B_84] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_1208])).

tff(c_1227,plain,(
    ! [B_84] :
      ( ~ v3_pre_topc(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_381,c_1214])).

tff(c_1235,plain,(
    ! [B_156] :
      ( ~ v3_pre_topc(B_156,'#skF_3')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1227])).

tff(c_1269,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_1235])).

tff(c_1272,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1269])).

tff(c_1276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.87  
% 3.40/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.88  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.40/1.88  
% 3.40/1.88  %Foreground sorts:
% 3.40/1.88  
% 3.40/1.88  
% 3.40/1.88  %Background operators:
% 3.40/1.88  
% 3.40/1.88  
% 3.40/1.88  %Foreground operators:
% 3.40/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.40/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.40/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.88  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.40/1.88  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.88  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.40/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/1.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.40/1.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.40/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.88  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.40/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.88  
% 3.40/1.90  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.40/1.90  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.40/1.90  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.40/1.90  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.40/1.90  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.40/1.90  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.90  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.40/1.90  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.40/1.90  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.40/1.90  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.40/1.90  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.40/1.90  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.40/1.90  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.40/1.90  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.40/1.90  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.40/1.90  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.40/1.90  tff(c_28, plain, (![A_23]: (v3_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.90  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.40/1.90  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.90  tff(c_53, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.40/1.90  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.40/1.90  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.40/1.90  tff(c_66, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.40/1.90  tff(c_75, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_66])).
% 3.40/1.90  tff(c_18, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.90  tff(c_77, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_18])).
% 3.40/1.90  tff(c_26, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.90  tff(c_94, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.90  tff(c_99, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_26, c_94])).
% 3.40/1.90  tff(c_103, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_99])).
% 3.40/1.90  tff(c_290, plain, (![A_93, B_94]: (r1_tarski('#skF_2'(A_93, B_94), B_94) | v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.40/1.90  tff(c_298, plain, (![B_94]: (r1_tarski('#skF_2'('#skF_3', B_94), B_94) | v2_tex_2(B_94, '#skF_3') | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_290])).
% 3.40/1.90  tff(c_359, plain, (![B_100]: (r1_tarski('#skF_2'('#skF_3', B_100), B_100) | v2_tex_2(B_100, '#skF_3') | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_298])).
% 3.40/1.90  tff(c_368, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_77, c_359])).
% 3.40/1.90  tff(c_376, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_368])).
% 3.40/1.90  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.90  tff(c_92, plain, (![A_2]: (A_2='#skF_4' | ~r1_tarski(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_6])).
% 3.40/1.90  tff(c_381, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_376, c_92])).
% 3.40/1.90  tff(c_136, plain, (![A_73, B_74, C_75]: (k9_subset_1(A_73, B_74, C_75)=k3_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.90  tff(c_146, plain, (![A_76, B_77]: (k9_subset_1(A_76, B_77, A_76)=k3_xboole_0(B_77, A_76))), inference(resolution, [status(thm)], [c_53, c_136])).
% 3.40/1.90  tff(c_14, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.90  tff(c_152, plain, (![B_77, A_76]: (m1_subset_1(k3_xboole_0(B_77, A_76), k1_zfmisc_1(A_76)) | ~m1_subset_1(A_76, k1_zfmisc_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_14])).
% 3.40/1.90  tff(c_160, plain, (![B_78, A_79]: (m1_subset_1(k3_xboole_0(B_78, A_79), k1_zfmisc_1(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_152])).
% 3.40/1.90  tff(c_20, plain, (![B_17, A_15]: (v1_xboole_0(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.90  tff(c_171, plain, (![B_80, A_81]: (v1_xboole_0(k3_xboole_0(B_80, A_81)) | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_160, c_20])).
% 3.40/1.90  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.40/1.90  tff(c_76, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_4])).
% 3.40/1.90  tff(c_190, plain, (![B_85, A_86]: (k3_xboole_0(B_85, A_86)='#skF_4' | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_171, c_76])).
% 3.40/1.90  tff(c_196, plain, (![B_85]: (k3_xboole_0(B_85, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_46, c_190])).
% 3.40/1.90  tff(c_144, plain, (![A_14, B_74]: (k9_subset_1(A_14, B_74, '#skF_4')=k3_xboole_0(B_74, '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_136])).
% 3.40/1.90  tff(c_236, plain, (![A_14, B_74]: (k9_subset_1(A_14, B_74, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_144])).
% 3.40/1.90  tff(c_176, plain, (![A_82, C_83, B_84]: (k9_subset_1(A_82, C_83, B_84)=k9_subset_1(A_82, B_84, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.90  tff(c_187, plain, (![A_14, B_84]: (k9_subset_1(A_14, B_84, '#skF_4')=k9_subset_1(A_14, '#skF_4', B_84))), inference(resolution, [status(thm)], [c_77, c_176])).
% 3.40/1.90  tff(c_312, plain, (![A_14, B_84]: (k9_subset_1(A_14, '#skF_4', B_84)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_187])).
% 3.40/1.90  tff(c_1177, plain, (![A_151, B_152, D_153]: (k9_subset_1(u1_struct_0(A_151), B_152, D_153)!='#skF_2'(A_151, B_152) | ~v3_pre_topc(D_153, A_151) | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0(A_151))) | v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.40/1.90  tff(c_1194, plain, (![B_152, D_153]: (k9_subset_1(k2_struct_0('#skF_3'), B_152, D_153)!='#skF_2'('#skF_3', B_152) | ~v3_pre_topc(D_153, '#skF_3') | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_152, '#skF_3') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_1177])).
% 3.40/1.90  tff(c_1208, plain, (![B_154, D_155]: (k9_subset_1(k2_struct_0('#skF_3'), B_154, D_155)!='#skF_2'('#skF_3', B_154) | ~v3_pre_topc(D_155, '#skF_3') | ~m1_subset_1(D_155, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2(B_154, '#skF_3') | ~m1_subset_1(B_154, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_103, c_103, c_1194])).
% 3.40/1.90  tff(c_1214, plain, (![B_84]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v3_pre_topc(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_312, c_1208])).
% 3.40/1.90  tff(c_1227, plain, (![B_84]: (~v3_pre_topc(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_381, c_1214])).
% 3.40/1.90  tff(c_1235, plain, (![B_156]: (~v3_pre_topc(B_156, '#skF_3') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1227])).
% 3.40/1.90  tff(c_1269, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_53, c_1235])).
% 3.40/1.90  tff(c_1272, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1269])).
% 3.40/1.90  tff(c_1276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1272])).
% 3.40/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.90  
% 3.40/1.90  Inference rules
% 3.40/1.90  ----------------------
% 3.40/1.90  #Ref     : 0
% 3.40/1.90  #Sup     : 290
% 3.40/1.90  #Fact    : 0
% 3.40/1.90  #Define  : 0
% 3.40/1.90  #Split   : 1
% 3.40/1.90  #Chain   : 0
% 3.40/1.90  #Close   : 0
% 3.40/1.90  
% 3.40/1.90  Ordering : KBO
% 3.40/1.90  
% 3.40/1.90  Simplification rules
% 3.40/1.90  ----------------------
% 3.40/1.90  #Subsume      : 30
% 3.40/1.90  #Demod        : 204
% 3.40/1.90  #Tautology    : 142
% 3.40/1.90  #SimpNegUnit  : 5
% 3.40/1.90  #BackRed      : 6
% 3.40/1.90  
% 3.40/1.90  #Partial instantiations: 0
% 3.40/1.90  #Strategies tried      : 1
% 3.40/1.90  
% 3.40/1.90  Timing (in seconds)
% 3.40/1.90  ----------------------
% 3.40/1.91  Preprocessing        : 0.45
% 3.40/1.91  Parsing              : 0.25
% 3.40/1.91  CNF conversion       : 0.03
% 3.40/1.91  Main loop            : 0.52
% 3.40/1.91  Inferencing          : 0.18
% 3.40/1.91  Reduction            : 0.17
% 3.40/1.91  Demodulation         : 0.13
% 3.40/1.91  BG Simplification    : 0.03
% 3.40/1.91  Subsumption          : 0.09
% 3.40/1.91  Abstraction          : 0.03
% 3.40/1.91  MUC search           : 0.00
% 3.40/1.91  Cooper               : 0.00
% 3.40/1.91  Total                : 1.03
% 3.40/1.91  Index Insertion      : 0.00
% 3.40/1.91  Index Deletion       : 0.00
% 3.40/1.91  Index Matching       : 0.00
% 3.40/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
