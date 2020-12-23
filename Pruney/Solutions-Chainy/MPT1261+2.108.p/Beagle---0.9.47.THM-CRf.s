%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:27 EST 2020

% Result     : Theorem 23.14s
% Output     : CNFRefutation 23.14s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 157 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 282 expanded)
%              Number of equality atoms :   67 ( 108 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_95588,plain,(
    ! [A_530,B_531,C_532] :
      ( k7_subset_1(A_530,B_531,C_532) = k4_xboole_0(B_531,C_532)
      | ~ m1_subset_1(B_531,k1_zfmisc_1(A_530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95595,plain,(
    ! [C_532] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_532) = k4_xboole_0('#skF_2',C_532) ),
    inference(resolution,[status(thm)],[c_38,c_95588])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_156,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2341,plain,(
    ! [B_120,A_121] :
      ( v4_pre_topc(B_120,A_121)
      | k2_pre_topc(A_121,B_120) != B_120
      | ~ v2_pre_topc(A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2347,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2341])).

tff(c_2359,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_2347])).

tff(c_2360,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2359])).

tff(c_512,plain,(
    ! [A_73,B_74,C_75] :
      ( k7_subset_1(A_73,B_74,C_75) = k4_xboole_0(B_74,C_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_560,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_38,c_512])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_204,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_50])).

tff(c_566,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_204])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_160,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [B_47] : k4_xboole_0(B_47,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_88])).

tff(c_176,plain,(
    ! [B_47] : k4_xboole_0(B_47,k1_xboole_0) = B_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_167])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_245,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = k3_subset_1(A_21,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_245])).

tff(c_257,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_251])).

tff(c_268,plain,(
    ! [A_63,B_64] :
      ( k3_subset_1(A_63,k3_subset_1(A_63,B_64)) = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_272,plain,(
    ! [A_21] : k3_subset_1(A_21,k3_subset_1(A_21,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_268])).

tff(c_277,plain,(
    ! [A_21] : k3_subset_1(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_272])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_258,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_subset_1(A_12,A_12) ),
    inference(resolution,[status(thm)],[c_51,c_245])).

tff(c_298,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_258])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_307,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,k4_xboole_0(A_6,B_7))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_8])).

tff(c_326,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,A_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_211,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8683,plain,(
    ! [C_194,A_195,B_196] : k2_xboole_0(C_194,k4_xboole_0(A_195,k2_xboole_0(B_196,C_194))) = k2_xboole_0(C_194,k4_xboole_0(A_195,B_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_6])).

tff(c_8976,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_8683])).

tff(c_9089,plain,(
    ! [A_197,B_198] : k2_xboole_0(A_197,k4_xboole_0(A_197,B_198)) = A_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8976])).

tff(c_9335,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_9089])).

tff(c_2549,plain,(
    ! [A_125,B_126] :
      ( k4_subset_1(u1_struct_0(A_125),B_126,k2_tops_1(A_125,B_126)) = k2_pre_topc(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2553,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2549])).

tff(c_2563,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2553])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2108,plain,(
    ! [A_114,B_115,C_116] :
      ( k4_subset_1(A_114,B_115,C_116) = k2_xboole_0(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25611,plain,(
    ! [A_299,B_300,B_301] :
      ( k4_subset_1(u1_struct_0(A_299),B_300,k2_tops_1(A_299,B_301)) = k2_xboole_0(B_300,k2_tops_1(A_299,B_301))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(resolution,[status(thm)],[c_30,c_2108])).

tff(c_25615,plain,(
    ! [B_301] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_301)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_301))
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_25611])).

tff(c_95425,plain,(
    ! [B_509] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_509)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_509))
      | ~ m1_subset_1(B_509,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25615])).

tff(c_95432,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_95425])).

tff(c_95445,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9335,c_2563,c_95432])).

tff(c_95447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2360,c_95445])).

tff(c_95448,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_95884,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95595,c_95448])).

tff(c_95449,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_95853,plain,(
    ! [A_542,B_543] :
      ( k2_pre_topc(A_542,B_543) = B_543
      | ~ v4_pre_topc(B_543,A_542)
      | ~ m1_subset_1(B_543,k1_zfmisc_1(u1_struct_0(A_542)))
      | ~ l1_pre_topc(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95856,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_95853])).

tff(c_95867,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95449,c_95856])).

tff(c_97888,plain,(
    ! [A_593,B_594] :
      ( k7_subset_1(u1_struct_0(A_593),k2_pre_topc(A_593,B_594),k1_tops_1(A_593,B_594)) = k2_tops_1(A_593,B_594)
      | ~ m1_subset_1(B_594,k1_zfmisc_1(u1_struct_0(A_593)))
      | ~ l1_pre_topc(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_97897,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95867,c_97888])).

tff(c_97901,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_95595,c_97897])).

tff(c_97903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95884,c_97901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.14/15.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/15.64  
% 23.14/15.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/15.64  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.14/15.64  
% 23.14/15.64  %Foreground sorts:
% 23.14/15.64  
% 23.14/15.64  
% 23.14/15.64  %Background operators:
% 23.14/15.64  
% 23.14/15.64  
% 23.14/15.64  %Foreground operators:
% 23.14/15.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.14/15.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.14/15.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.14/15.64  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.14/15.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.14/15.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.14/15.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.14/15.64  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.14/15.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 23.14/15.64  tff('#skF_2', type, '#skF_2': $i).
% 23.14/15.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 23.14/15.64  tff('#skF_1', type, '#skF_1': $i).
% 23.14/15.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.14/15.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.14/15.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.14/15.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.14/15.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.14/15.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.14/15.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.14/15.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.14/15.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.14/15.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.14/15.64  
% 23.14/15.66  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 23.14/15.66  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 23.14/15.66  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 23.14/15.66  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 23.14/15.66  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 23.14/15.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 23.14/15.66  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 23.14/15.66  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 23.14/15.66  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 23.14/15.66  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 23.14/15.66  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 23.14/15.66  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 23.14/15.66  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 23.14/15.66  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 23.14/15.66  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.14/15.66  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 23.14/15.66  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.14/15.66  tff(c_95588, plain, (![A_530, B_531, C_532]: (k7_subset_1(A_530, B_531, C_532)=k4_xboole_0(B_531, C_532) | ~m1_subset_1(B_531, k1_zfmisc_1(A_530)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.14/15.66  tff(c_95595, plain, (![C_532]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_532)=k4_xboole_0('#skF_2', C_532))), inference(resolution, [status(thm)], [c_38, c_95588])).
% 23.14/15.66  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.14/15.66  tff(c_156, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 23.14/15.66  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.14/15.66  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.14/15.66  tff(c_2341, plain, (![B_120, A_121]: (v4_pre_topc(B_120, A_121) | k2_pre_topc(A_121, B_120)!=B_120 | ~v2_pre_topc(A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.14/15.66  tff(c_2347, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2341])).
% 23.14/15.66  tff(c_2359, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_2347])).
% 23.14/15.66  tff(c_2360, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_156, c_2359])).
% 23.14/15.66  tff(c_512, plain, (![A_73, B_74, C_75]: (k7_subset_1(A_73, B_74, C_75)=k4_xboole_0(B_74, C_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.14/15.66  tff(c_560, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_38, c_512])).
% 23.14/15.66  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.14/15.66  tff(c_204, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_156, c_50])).
% 23.14/15.66  tff(c_566, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_560, c_204])).
% 23.14/15.66  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.14/15.66  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.14/15.66  tff(c_72, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.14/15.66  tff(c_88, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 23.14/15.66  tff(c_160, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.14/15.66  tff(c_167, plain, (![B_47]: (k4_xboole_0(B_47, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_160, c_88])).
% 23.14/15.66  tff(c_176, plain, (![B_47]: (k4_xboole_0(B_47, k1_xboole_0)=B_47)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_167])).
% 23.14/15.66  tff(c_22, plain, (![A_21]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.14/15.66  tff(c_245, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.14/15.66  tff(c_251, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=k3_subset_1(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_245])).
% 23.14/15.66  tff(c_257, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_176, c_251])).
% 23.14/15.66  tff(c_268, plain, (![A_63, B_64]: (k3_subset_1(A_63, k3_subset_1(A_63, B_64))=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.14/15.66  tff(c_272, plain, (![A_21]: (k3_subset_1(A_21, k3_subset_1(A_21, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_268])).
% 23.14/15.66  tff(c_277, plain, (![A_21]: (k3_subset_1(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_272])).
% 23.14/15.66  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.14/15.66  tff(c_14, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.14/15.66  tff(c_51, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 23.14/15.66  tff(c_258, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_subset_1(A_12, A_12))), inference(resolution, [status(thm)], [c_51, c_245])).
% 23.14/15.66  tff(c_298, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_277, c_258])).
% 23.14/15.66  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.14/15.66  tff(c_307, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, k4_xboole_0(A_6, B_7)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_298, c_8])).
% 23.14/15.66  tff(c_326, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, A_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 23.14/15.66  tff(c_211, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.14/15.66  tff(c_8683, plain, (![C_194, A_195, B_196]: (k2_xboole_0(C_194, k4_xboole_0(A_195, k2_xboole_0(B_196, C_194)))=k2_xboole_0(C_194, k4_xboole_0(A_195, B_196)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_6])).
% 23.14/15.66  tff(c_8976, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_326, c_8683])).
% 23.14/15.66  tff(c_9089, plain, (![A_197, B_198]: (k2_xboole_0(A_197, k4_xboole_0(A_197, B_198))=A_197)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8976])).
% 23.14/15.66  tff(c_9335, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_566, c_9089])).
% 23.14/15.66  tff(c_2549, plain, (![A_125, B_126]: (k4_subset_1(u1_struct_0(A_125), B_126, k2_tops_1(A_125, B_126))=k2_pre_topc(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_106])).
% 23.14/15.66  tff(c_2553, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2549])).
% 23.14/15.66  tff(c_2563, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2553])).
% 23.14/15.66  tff(c_30, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 23.14/15.66  tff(c_2108, plain, (![A_114, B_115, C_116]: (k4_subset_1(A_114, B_115, C_116)=k2_xboole_0(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.14/15.66  tff(c_25611, plain, (![A_299, B_300, B_301]: (k4_subset_1(u1_struct_0(A_299), B_300, k2_tops_1(A_299, B_301))=k2_xboole_0(B_300, k2_tops_1(A_299, B_301)) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(resolution, [status(thm)], [c_30, c_2108])).
% 23.14/15.66  tff(c_25615, plain, (![B_301]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_301))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_301)) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_25611])).
% 23.14/15.66  tff(c_95425, plain, (![B_509]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_509))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_509)) | ~m1_subset_1(B_509, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25615])).
% 23.14/15.66  tff(c_95432, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_95425])).
% 23.14/15.66  tff(c_95445, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9335, c_2563, c_95432])).
% 23.14/15.66  tff(c_95447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2360, c_95445])).
% 23.14/15.66  tff(c_95448, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 23.14/15.66  tff(c_95884, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95595, c_95448])).
% 23.14/15.66  tff(c_95449, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 23.14/15.66  tff(c_95853, plain, (![A_542, B_543]: (k2_pre_topc(A_542, B_543)=B_543 | ~v4_pre_topc(B_543, A_542) | ~m1_subset_1(B_543, k1_zfmisc_1(u1_struct_0(A_542))) | ~l1_pre_topc(A_542))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.14/15.66  tff(c_95856, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_95853])).
% 23.14/15.66  tff(c_95867, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95449, c_95856])).
% 23.14/15.66  tff(c_97888, plain, (![A_593, B_594]: (k7_subset_1(u1_struct_0(A_593), k2_pre_topc(A_593, B_594), k1_tops_1(A_593, B_594))=k2_tops_1(A_593, B_594) | ~m1_subset_1(B_594, k1_zfmisc_1(u1_struct_0(A_593))) | ~l1_pre_topc(A_593))), inference(cnfTransformation, [status(thm)], [f_99])).
% 23.14/15.66  tff(c_97897, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95867, c_97888])).
% 23.14/15.66  tff(c_97901, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_95595, c_97897])).
% 23.14/15.66  tff(c_97903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95884, c_97901])).
% 23.14/15.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.14/15.66  
% 23.14/15.66  Inference rules
% 23.14/15.66  ----------------------
% 23.14/15.66  #Ref     : 0
% 23.14/15.66  #Sup     : 24430
% 23.14/15.66  #Fact    : 0
% 23.14/15.66  #Define  : 0
% 23.14/15.66  #Split   : 2
% 23.14/15.66  #Chain   : 0
% 23.14/15.66  #Close   : 0
% 23.14/15.66  
% 23.14/15.66  Ordering : KBO
% 23.14/15.66  
% 23.14/15.66  Simplification rules
% 23.14/15.66  ----------------------
% 23.14/15.66  #Subsume      : 332
% 23.14/15.67  #Demod        : 33814
% 23.14/15.67  #Tautology    : 16194
% 23.14/15.67  #SimpNegUnit  : 4
% 23.14/15.67  #BackRed      : 5
% 23.14/15.67  
% 23.14/15.67  #Partial instantiations: 0
% 23.14/15.67  #Strategies tried      : 1
% 23.14/15.67  
% 23.14/15.67  Timing (in seconds)
% 23.14/15.67  ----------------------
% 23.14/15.67  Preprocessing        : 0.33
% 23.14/15.67  Parsing              : 0.18
% 23.14/15.67  CNF conversion       : 0.02
% 23.14/15.67  Main loop            : 14.48
% 23.14/15.67  Inferencing          : 1.57
% 23.14/15.67  Reduction            : 10.04
% 23.14/15.67  Demodulation         : 9.43
% 23.14/15.67  BG Simplification    : 0.19
% 23.14/15.67  Subsumption          : 2.26
% 23.14/15.67  Abstraction          : 0.39
% 23.14/15.67  MUC search           : 0.00
% 23.14/15.67  Cooper               : 0.00
% 23.14/15.67  Total                : 14.85
% 23.14/15.67  Index Insertion      : 0.00
% 23.14/15.67  Index Deletion       : 0.00
% 23.14/15.67  Index Matching       : 0.00
% 23.14/15.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
