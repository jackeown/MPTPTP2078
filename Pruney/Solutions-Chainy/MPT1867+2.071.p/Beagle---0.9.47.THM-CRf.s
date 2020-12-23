%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 168 expanded)
%              Number of leaves         :   40 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 328 expanded)
%              Number of equality atoms :   34 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_24] :
      ( v4_pre_topc(k2_struct_0(A_24),A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_44,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_66,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_22,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    ! [A_18] : m1_subset_1('#skF_4',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_22])).

tff(c_28,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_173,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_177,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_173])).

tff(c_355,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_357,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_2'('#skF_3',B_89),B_89)
      | v2_tex_2(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_355])).

tff(c_588,plain,(
    ! [B_106] :
      ( r1_tarski('#skF_2'('#skF_3',B_106),B_106)
      | v2_tex_2(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_357])).

tff(c_594,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_588])).

tff(c_598,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_594])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_10])).

tff(c_602,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_598,c_100])).

tff(c_183,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_60] :
      ( A_60 = '#skF_4'
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_10])).

tff(c_106,plain,(
    ! [B_5] : k4_xboole_0('#skF_4',B_5) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_216,plain,(
    ! [B_70] : k3_xboole_0('#skF_4',B_70) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_106])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_224,plain,(
    ! [B_70] : k3_xboole_0(B_70,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_2])).

tff(c_279,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,C_77) = k3_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_283,plain,(
    ! [A_18,B_76] : k9_subset_1(A_18,B_76,'#skF_4') = k3_xboole_0(B_76,'#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_279])).

tff(c_286,plain,(
    ! [A_18,B_76] : k9_subset_1(A_18,B_76,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_283])).

tff(c_317,plain,(
    ! [A_81,C_82,B_83] :
      ( k9_subset_1(A_81,C_82,B_83) = k9_subset_1(A_81,B_83,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_323,plain,(
    ! [A_18,B_83] : k9_subset_1(A_18,B_83,'#skF_4') = k9_subset_1(A_18,'#skF_4',B_83) ),
    inference(resolution,[status(thm)],[c_86,c_317])).

tff(c_508,plain,(
    ! [A_18,B_83] : k9_subset_1(A_18,'#skF_4',B_83) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_323])).

tff(c_1317,plain,(
    ! [A_135,B_136,D_137] :
      ( k9_subset_1(u1_struct_0(A_135),B_136,D_137) != '#skF_2'(A_135,B_136)
      | ~ v4_pre_topc(D_137,A_135)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1331,plain,(
    ! [B_136,D_137] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_136,D_137) != '#skF_2'('#skF_3',B_136)
      | ~ v4_pre_topc(D_137,'#skF_3')
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_1317])).

tff(c_1420,plain,(
    ! [B_140,D_141] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_140,D_141) != '#skF_2'('#skF_3',B_140)
      | ~ v4_pre_topc(D_141,'#skF_3')
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_140,'#skF_3')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_177,c_177,c_1331])).

tff(c_1423,plain,(
    ! [B_83] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_1420])).

tff(c_1434,plain,(
    ! [B_83] :
      ( ~ v4_pre_topc(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_602,c_1423])).

tff(c_1442,plain,(
    ! [B_142] :
      ( ~ v4_pre_topc(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1434])).

tff(c_1455,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_1442])).

tff(c_1459,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1455])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.71  
% 3.54/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.72  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.54/1.72  
% 3.54/1.72  %Foreground sorts:
% 3.54/1.72  
% 3.54/1.72  
% 3.54/1.72  %Background operators:
% 3.54/1.72  
% 3.54/1.72  
% 3.54/1.72  %Foreground operators:
% 3.54/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.54/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.54/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.72  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.54/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.54/1.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.54/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.54/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.54/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.54/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.72  
% 3.54/1.73  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.54/1.73  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.54/1.73  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.54/1.73  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.54/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.54/1.73  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.54/1.73  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.73  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.54/1.73  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.54/1.73  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.54/1.73  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.54/1.73  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.54/1.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/1.73  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.54/1.73  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.54/1.73  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.54/1.73  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.54/1.73  tff(c_30, plain, (![A_24]: (v4_pre_topc(k2_struct_0(A_24), A_24) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.73  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.73  tff(c_18, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.54/1.73  tff(c_55, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 3.54/1.73  tff(c_44, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.54/1.73  tff(c_48, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.54/1.73  tff(c_66, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.73  tff(c_70, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_48, c_66])).
% 3.54/1.73  tff(c_22, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.54/1.73  tff(c_86, plain, (![A_18]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_22])).
% 3.54/1.73  tff(c_28, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.73  tff(c_135, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.73  tff(c_173, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_28, c_135])).
% 3.54/1.73  tff(c_177, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_173])).
% 3.54/1.73  tff(c_355, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.73  tff(c_357, plain, (![B_89]: (r1_tarski('#skF_2'('#skF_3', B_89), B_89) | v2_tex_2(B_89, '#skF_3') | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_355])).
% 3.54/1.73  tff(c_588, plain, (![B_106]: (r1_tarski('#skF_2'('#skF_3', B_106), B_106) | v2_tex_2(B_106, '#skF_3') | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_357])).
% 3.54/1.73  tff(c_594, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_588])).
% 3.54/1.73  tff(c_598, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_594])).
% 3.54/1.73  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.73  tff(c_100, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_10])).
% 3.54/1.73  tff(c_602, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_598, c_100])).
% 3.54/1.73  tff(c_183, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.73  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.73  tff(c_101, plain, (![A_60]: (A_60='#skF_4' | ~r1_tarski(A_60, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_10])).
% 3.54/1.73  tff(c_106, plain, (![B_5]: (k4_xboole_0('#skF_4', B_5)='#skF_4')), inference(resolution, [status(thm)], [c_6, c_101])).
% 3.54/1.73  tff(c_216, plain, (![B_70]: (k3_xboole_0('#skF_4', B_70)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_106])).
% 3.54/1.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.73  tff(c_224, plain, (![B_70]: (k3_xboole_0(B_70, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_216, c_2])).
% 3.54/1.73  tff(c_279, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, C_77)=k3_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.73  tff(c_283, plain, (![A_18, B_76]: (k9_subset_1(A_18, B_76, '#skF_4')=k3_xboole_0(B_76, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_279])).
% 3.54/1.73  tff(c_286, plain, (![A_18, B_76]: (k9_subset_1(A_18, B_76, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_283])).
% 3.54/1.73  tff(c_317, plain, (![A_81, C_82, B_83]: (k9_subset_1(A_81, C_82, B_83)=k9_subset_1(A_81, B_83, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.73  tff(c_323, plain, (![A_18, B_83]: (k9_subset_1(A_18, B_83, '#skF_4')=k9_subset_1(A_18, '#skF_4', B_83))), inference(resolution, [status(thm)], [c_86, c_317])).
% 3.54/1.73  tff(c_508, plain, (![A_18, B_83]: (k9_subset_1(A_18, '#skF_4', B_83)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_323])).
% 3.54/1.73  tff(c_1317, plain, (![A_135, B_136, D_137]: (k9_subset_1(u1_struct_0(A_135), B_136, D_137)!='#skF_2'(A_135, B_136) | ~v4_pre_topc(D_137, A_135) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_135))) | v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.73  tff(c_1331, plain, (![B_136, D_137]: (k9_subset_1(k2_struct_0('#skF_3'), B_136, D_137)!='#skF_2'('#skF_3', B_136) | ~v4_pre_topc(D_137, '#skF_3') | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_1317])).
% 3.54/1.73  tff(c_1420, plain, (![B_140, D_141]: (k9_subset_1(k2_struct_0('#skF_3'), B_140, D_141)!='#skF_2'('#skF_3', B_140) | ~v4_pre_topc(D_141, '#skF_3') | ~m1_subset_1(D_141, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2(B_140, '#skF_3') | ~m1_subset_1(B_140, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_177, c_177, c_1331])).
% 3.54/1.73  tff(c_1423, plain, (![B_83]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v4_pre_topc(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_508, c_1420])).
% 3.54/1.73  tff(c_1434, plain, (![B_83]: (~v4_pre_topc(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_602, c_1423])).
% 3.54/1.73  tff(c_1442, plain, (![B_142]: (~v4_pre_topc(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_1434])).
% 3.54/1.73  tff(c_1455, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_1442])).
% 3.54/1.73  tff(c_1459, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1455])).
% 3.54/1.73  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1459])).
% 3.54/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.73  
% 3.54/1.73  Inference rules
% 3.54/1.73  ----------------------
% 3.54/1.73  #Ref     : 0
% 3.54/1.73  #Sup     : 329
% 3.54/1.73  #Fact    : 0
% 3.54/1.73  #Define  : 0
% 3.54/1.73  #Split   : 1
% 3.54/1.73  #Chain   : 0
% 3.54/1.73  #Close   : 0
% 3.54/1.73  
% 3.54/1.73  Ordering : KBO
% 3.54/1.73  
% 3.54/1.73  Simplification rules
% 3.54/1.73  ----------------------
% 3.54/1.73  #Subsume      : 4
% 3.54/1.73  #Demod        : 338
% 3.54/1.73  #Tautology    : 223
% 3.54/1.73  #SimpNegUnit  : 5
% 3.54/1.73  #BackRed      : 2
% 3.54/1.73  
% 3.54/1.73  #Partial instantiations: 0
% 3.54/1.73  #Strategies tried      : 1
% 3.54/1.73  
% 3.54/1.73  Timing (in seconds)
% 3.54/1.73  ----------------------
% 3.54/1.73  Preprocessing        : 0.38
% 3.54/1.73  Parsing              : 0.21
% 3.54/1.73  CNF conversion       : 0.03
% 3.54/1.73  Main loop            : 0.48
% 3.54/1.73  Inferencing          : 0.15
% 3.54/1.73  Reduction            : 0.20
% 3.54/1.73  Demodulation         : 0.16
% 3.54/1.73  BG Simplification    : 0.03
% 3.54/1.73  Subsumption          : 0.07
% 3.54/1.73  Abstraction          : 0.03
% 3.54/1.73  MUC search           : 0.00
% 3.54/1.73  Cooper               : 0.00
% 3.54/1.73  Total                : 0.89
% 3.54/1.73  Index Insertion      : 0.00
% 3.54/1.73  Index Deletion       : 0.00
% 3.54/1.73  Index Matching       : 0.00
% 3.54/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
