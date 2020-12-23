%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 19.05s
% Output     : CNFRefutation 19.05s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 425 expanded)
%              Number of leaves         :   35 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 ( 873 expanded)
%              Number of equality atoms :   27 ( 144 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_84,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [A_71,A_72] :
      ( ~ v1_xboole_0(A_71)
      | ~ r2_hidden(A_72,A_71) ) ),
    inference(resolution,[status(thm)],[c_53,c_84])).

tff(c_114,plain,(
    ! [A_73,B_74] :
      ( ~ v1_xboole_0(A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_75] :
      ( k1_xboole_0 = A_75
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_120])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [A_18] : m1_subset_1('#skF_5',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_412,plain,(
    ! [A_118,B_119] :
      ( r1_tarski('#skF_3'(A_118,B_119),B_119)
      | v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_485,plain,(
    ! [A_125] :
      ( r1_tarski('#skF_3'(A_125,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_134,c_412])).

tff(c_133,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ r1_tarski(A_6,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_10])).

tff(c_490,plain,(
    ! [A_126] :
      ( '#skF_3'(A_126,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_485,c_133])).

tff(c_493,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_490,c_42])).

tff(c_496,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_493])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_507,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_3'(A_127,B_128),k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    ! [B_27,A_25] :
      ( v4_pre_topc(B_27,A_25)
      | ~ v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6336,plain,(
    ! [A_365,B_366] :
      ( v4_pre_topc('#skF_3'(A_365,B_366),A_365)
      | ~ v1_xboole_0('#skF_3'(A_365,B_366))
      | ~ v2_pre_topc(A_365)
      | v2_tex_2(B_366,A_365)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365) ) ),
    inference(resolution,[status(thm)],[c_507,c_28])).

tff(c_22956,plain,(
    ! [A_718] :
      ( v4_pre_topc('#skF_3'(A_718,'#skF_5'),A_718)
      | ~ v1_xboole_0('#skF_3'(A_718,'#skF_5'))
      | ~ v2_pre_topc(A_718)
      | v2_tex_2('#skF_5',A_718)
      | ~ l1_pre_topc(A_718) ) ),
    inference(resolution,[status(thm)],[c_134,c_6336])).

tff(c_22959,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_22956])).

tff(c_22961,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_46,c_496,c_22959])).

tff(c_22962,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_22961])).

tff(c_202,plain,(
    ! [A_88,B_89,C_90] :
      ( k9_subset_1(A_88,B_89,C_90) = k3_xboole_0(B_89,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_94,B_95] : k9_subset_1(A_94,B_95,A_94) = k3_xboole_0(B_95,A_94) ),
    inference(resolution,[status(thm)],[c_53,c_202])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k9_subset_1(A_12,B_13,C_14),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_229,plain,(
    ! [B_95,A_94] :
      ( m1_subset_1(k3_xboole_0(B_95,A_94),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(A_94,k1_zfmisc_1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_18])).

tff(c_237,plain,(
    ! [B_96,A_97] : m1_subset_1(k3_xboole_0(B_96,A_97),k1_zfmisc_1(A_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_229])).

tff(c_26,plain,(
    ! [C_24,B_23,A_22] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_247,plain,(
    ! [A_98,A_99,B_100] :
      ( ~ v1_xboole_0(A_98)
      | ~ r2_hidden(A_99,k3_xboole_0(B_100,A_98)) ) ),
    inference(resolution,[status(thm)],[c_237,c_26])).

tff(c_294,plain,(
    ! [A_106,B_107,B_108] :
      ( ~ v1_xboole_0(A_106)
      | r1_tarski(k3_xboole_0(B_107,A_106),B_108) ) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_300,plain,(
    ! [B_109,A_110] :
      ( k3_xboole_0(B_109,A_110) = '#skF_5'
      | ~ v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_294,c_133])).

tff(c_303,plain,(
    ! [B_109] : k3_xboole_0(B_109,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_300])).

tff(c_211,plain,(
    ! [A_18,B_89] : k9_subset_1(A_18,B_89,'#skF_5') = k3_xboole_0(B_89,'#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_202])).

tff(c_325,plain,(
    ! [A_18,B_89] : k9_subset_1(A_18,B_89,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_211])).

tff(c_253,plain,(
    ! [A_101,C_102,B_103] :
      ( k9_subset_1(A_101,C_102,B_103) = k9_subset_1(A_101,B_103,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_268,plain,(
    ! [A_18,B_103] : k9_subset_1(A_18,B_103,'#skF_5') = k9_subset_1(A_18,'#skF_5',B_103) ),
    inference(resolution,[status(thm)],[c_134,c_253])).

tff(c_445,plain,(
    ! [A_18,B_103] : k9_subset_1(A_18,'#skF_5',B_103) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_268])).

tff(c_710,plain,(
    ! [A_150,B_151,D_152] :
      ( k9_subset_1(u1_struct_0(A_150),B_151,D_152) != '#skF_3'(A_150,B_151)
      | ~ v4_pre_topc(D_152,A_150)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(A_150)))
      | v2_tex_2(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_713,plain,(
    ! [A_150,B_103] :
      ( '#skF_3'(A_150,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_103,A_150)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_150)))
      | v2_tex_2('#skF_5',A_150)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_710])).

tff(c_76607,plain,(
    ! [A_1313,B_1314] :
      ( '#skF_3'(A_1313,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_1314,A_1313)
      | ~ m1_subset_1(B_1314,k1_zfmisc_1(u1_struct_0(A_1313)))
      | v2_tex_2('#skF_5',A_1313)
      | ~ l1_pre_topc(A_1313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_713])).

tff(c_76761,plain,(
    ! [A_1315] :
      ( '#skF_3'(A_1315,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_1315)
      | v2_tex_2('#skF_5',A_1315)
      | ~ l1_pre_topc(A_1315) ) ),
    inference(resolution,[status(thm)],[c_134,c_76607])).

tff(c_76764,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22962,c_76761])).

tff(c_76770,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_496,c_76764])).

tff(c_76772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_76770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.05/10.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.05/10.74  
% 19.05/10.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.05/10.74  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 19.05/10.74  
% 19.05/10.74  %Foreground sorts:
% 19.05/10.74  
% 19.05/10.74  
% 19.05/10.74  %Background operators:
% 19.05/10.74  
% 19.05/10.74  
% 19.05/10.74  %Foreground operators:
% 19.05/10.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.05/10.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.05/10.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.05/10.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.05/10.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.05/10.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.05/10.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.05/10.74  tff('#skF_5', type, '#skF_5': $i).
% 19.05/10.74  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 19.05/10.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.05/10.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.05/10.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 19.05/10.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.05/10.74  tff('#skF_4', type, '#skF_4': $i).
% 19.05/10.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.05/10.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.05/10.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.05/10.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.05/10.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.05/10.74  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.05/10.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.05/10.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.05/10.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.05/10.74  
% 19.05/10.76  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 19.05/10.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.05/10.76  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 19.05/10.76  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 19.05/10.76  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 19.05/10.76  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 19.05/10.76  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 19.05/10.76  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 19.05/10.76  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 19.05/10.76  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.05/10.76  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 19.05/10.76  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 19.05/10.76  tff(c_42, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.05/10.76  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.05/10.76  tff(c_46, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.05/10.76  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.05/10.76  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.05/10.76  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.05/10.76  tff(c_53, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 19.05/10.76  tff(c_84, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 19.05/10.76  tff(c_109, plain, (![A_71, A_72]: (~v1_xboole_0(A_71) | ~r2_hidden(A_72, A_71))), inference(resolution, [status(thm)], [c_53, c_84])).
% 19.05/10.76  tff(c_114, plain, (![A_73, B_74]: (~v1_xboole_0(A_73) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_109])).
% 19.05/10.76  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.05/10.76  tff(c_120, plain, (![A_75]: (k1_xboole_0=A_75 | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_114, c_10])).
% 19.05/10.76  tff(c_129, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_120])).
% 19.05/10.76  tff(c_22, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.05/10.76  tff(c_134, plain, (![A_18]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_22])).
% 19.05/10.76  tff(c_412, plain, (![A_118, B_119]: (r1_tarski('#skF_3'(A_118, B_119), B_119) | v2_tex_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.05/10.76  tff(c_485, plain, (![A_125]: (r1_tarski('#skF_3'(A_125, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_125) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_134, c_412])).
% 19.05/10.76  tff(c_133, plain, (![A_6]: (A_6='#skF_5' | ~r1_tarski(A_6, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_10])).
% 19.05/10.76  tff(c_490, plain, (![A_126]: ('#skF_3'(A_126, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_126) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_485, c_133])).
% 19.05/10.76  tff(c_493, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_490, c_42])).
% 19.05/10.76  tff(c_496, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_493])).
% 19.05/10.76  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.05/10.76  tff(c_507, plain, (![A_127, B_128]: (m1_subset_1('#skF_3'(A_127, B_128), k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.05/10.76  tff(c_28, plain, (![B_27, A_25]: (v4_pre_topc(B_27, A_25) | ~v1_xboole_0(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.05/10.76  tff(c_6336, plain, (![A_365, B_366]: (v4_pre_topc('#skF_3'(A_365, B_366), A_365) | ~v1_xboole_0('#skF_3'(A_365, B_366)) | ~v2_pre_topc(A_365) | v2_tex_2(B_366, A_365) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365))), inference(resolution, [status(thm)], [c_507, c_28])).
% 19.05/10.76  tff(c_22956, plain, (![A_718]: (v4_pre_topc('#skF_3'(A_718, '#skF_5'), A_718) | ~v1_xboole_0('#skF_3'(A_718, '#skF_5')) | ~v2_pre_topc(A_718) | v2_tex_2('#skF_5', A_718) | ~l1_pre_topc(A_718))), inference(resolution, [status(thm)], [c_134, c_6336])).
% 19.05/10.76  tff(c_22959, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_496, c_22956])).
% 19.05/10.76  tff(c_22961, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_46, c_496, c_22959])).
% 19.05/10.76  tff(c_22962, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_22961])).
% 19.05/10.76  tff(c_202, plain, (![A_88, B_89, C_90]: (k9_subset_1(A_88, B_89, C_90)=k3_xboole_0(B_89, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 19.05/10.76  tff(c_223, plain, (![A_94, B_95]: (k9_subset_1(A_94, B_95, A_94)=k3_xboole_0(B_95, A_94))), inference(resolution, [status(thm)], [c_53, c_202])).
% 19.05/10.76  tff(c_18, plain, (![A_12, B_13, C_14]: (m1_subset_1(k9_subset_1(A_12, B_13, C_14), k1_zfmisc_1(A_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.05/10.76  tff(c_229, plain, (![B_95, A_94]: (m1_subset_1(k3_xboole_0(B_95, A_94), k1_zfmisc_1(A_94)) | ~m1_subset_1(A_94, k1_zfmisc_1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_223, c_18])).
% 19.05/10.76  tff(c_237, plain, (![B_96, A_97]: (m1_subset_1(k3_xboole_0(B_96, A_97), k1_zfmisc_1(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_229])).
% 19.05/10.76  tff(c_26, plain, (![C_24, B_23, A_22]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(C_24)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 19.05/10.76  tff(c_247, plain, (![A_98, A_99, B_100]: (~v1_xboole_0(A_98) | ~r2_hidden(A_99, k3_xboole_0(B_100, A_98)))), inference(resolution, [status(thm)], [c_237, c_26])).
% 19.05/10.76  tff(c_294, plain, (![A_106, B_107, B_108]: (~v1_xboole_0(A_106) | r1_tarski(k3_xboole_0(B_107, A_106), B_108))), inference(resolution, [status(thm)], [c_6, c_247])).
% 19.05/10.76  tff(c_300, plain, (![B_109, A_110]: (k3_xboole_0(B_109, A_110)='#skF_5' | ~v1_xboole_0(A_110))), inference(resolution, [status(thm)], [c_294, c_133])).
% 19.05/10.76  tff(c_303, plain, (![B_109]: (k3_xboole_0(B_109, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_46, c_300])).
% 19.05/10.76  tff(c_211, plain, (![A_18, B_89]: (k9_subset_1(A_18, B_89, '#skF_5')=k3_xboole_0(B_89, '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_202])).
% 19.05/10.76  tff(c_325, plain, (![A_18, B_89]: (k9_subset_1(A_18, B_89, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_211])).
% 19.05/10.76  tff(c_253, plain, (![A_101, C_102, B_103]: (k9_subset_1(A_101, C_102, B_103)=k9_subset_1(A_101, B_103, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.05/10.76  tff(c_268, plain, (![A_18, B_103]: (k9_subset_1(A_18, B_103, '#skF_5')=k9_subset_1(A_18, '#skF_5', B_103))), inference(resolution, [status(thm)], [c_134, c_253])).
% 19.05/10.76  tff(c_445, plain, (![A_18, B_103]: (k9_subset_1(A_18, '#skF_5', B_103)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_268])).
% 19.05/10.76  tff(c_710, plain, (![A_150, B_151, D_152]: (k9_subset_1(u1_struct_0(A_150), B_151, D_152)!='#skF_3'(A_150, B_151) | ~v4_pre_topc(D_152, A_150) | ~m1_subset_1(D_152, k1_zfmisc_1(u1_struct_0(A_150))) | v2_tex_2(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.05/10.76  tff(c_713, plain, (![A_150, B_103]: ('#skF_3'(A_150, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_103, A_150) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_150))) | v2_tex_2('#skF_5', A_150) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(superposition, [status(thm), theory('equality')], [c_445, c_710])).
% 19.05/10.76  tff(c_76607, plain, (![A_1313, B_1314]: ('#skF_3'(A_1313, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_1314, A_1313) | ~m1_subset_1(B_1314, k1_zfmisc_1(u1_struct_0(A_1313))) | v2_tex_2('#skF_5', A_1313) | ~l1_pre_topc(A_1313))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_713])).
% 19.05/10.76  tff(c_76761, plain, (![A_1315]: ('#skF_3'(A_1315, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_1315) | v2_tex_2('#skF_5', A_1315) | ~l1_pre_topc(A_1315))), inference(resolution, [status(thm)], [c_134, c_76607])).
% 19.05/10.76  tff(c_76764, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22962, c_76761])).
% 19.05/10.76  tff(c_76770, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_496, c_76764])).
% 19.05/10.76  tff(c_76772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_76770])).
% 19.05/10.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.05/10.76  
% 19.05/10.76  Inference rules
% 19.05/10.76  ----------------------
% 19.05/10.76  #Ref     : 0
% 19.05/10.76  #Sup     : 18763
% 19.05/10.76  #Fact    : 2
% 19.05/10.76  #Define  : 0
% 19.05/10.76  #Split   : 5
% 19.05/10.76  #Chain   : 0
% 19.05/10.76  #Close   : 0
% 19.05/10.76  
% 19.05/10.76  Ordering : KBO
% 19.05/10.76  
% 19.05/10.76  Simplification rules
% 19.05/10.76  ----------------------
% 19.05/10.76  #Subsume      : 5890
% 19.05/10.76  #Demod        : 25625
% 19.05/10.76  #Tautology    : 7175
% 19.05/10.76  #SimpNegUnit  : 39
% 19.05/10.76  #BackRed      : 10
% 19.05/10.76  
% 19.05/10.76  #Partial instantiations: 0
% 19.05/10.76  #Strategies tried      : 1
% 19.05/10.76  
% 19.05/10.76  Timing (in seconds)
% 19.05/10.76  ----------------------
% 19.05/10.76  Preprocessing        : 0.32
% 19.05/10.76  Parsing              : 0.17
% 19.05/10.76  CNF conversion       : 0.02
% 19.05/10.76  Main loop            : 9.67
% 19.05/10.76  Inferencing          : 1.97
% 19.05/10.76  Reduction            : 4.17
% 19.05/10.76  Demodulation         : 3.57
% 19.05/10.76  BG Simplification    : 0.21
% 19.05/10.76  Subsumption          : 2.84
% 19.05/10.76  Abstraction          : 0.37
% 19.05/10.76  MUC search           : 0.00
% 19.05/10.76  Cooper               : 0.00
% 19.05/10.76  Total                : 10.02
% 19.05/10.76  Index Insertion      : 0.00
% 19.05/10.76  Index Deletion       : 0.00
% 19.05/10.76  Index Matching       : 0.00
% 19.05/10.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
