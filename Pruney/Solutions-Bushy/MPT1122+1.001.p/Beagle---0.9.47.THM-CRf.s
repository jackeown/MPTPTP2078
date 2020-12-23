%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1122+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 172 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 ( 533 expanded)
%              Number of equality atoms :   25 (  93 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
              & ( ( v2_pre_topc(A)
                  & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
               => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_4] :
      ( m1_subset_1(k2_struct_0(A_4),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,
    ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_28])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k7_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [B_24,A_25] :
      ( v4_pre_topc(B_24,A_25)
      | k2_pre_topc(A_25,B_24) != B_24
      | ~ v2_pre_topc(A_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,(
    ! [A_25,B_6,C_7] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_25),B_6,C_7),A_25)
      | k2_pre_topc(A_25,k7_subset_1(u1_struct_0(A_25),B_6,C_7)) != k7_subset_1(u1_struct_0(A_25),B_6,C_7)
      | ~ v2_pre_topc(A_25)
      | ~ l1_pre_topc(A_25)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_25))) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_90,plain,(
    ! [A_31,B_32] :
      ( k7_subset_1(u1_struct_0(A_31),k2_struct_0(A_31),k7_subset_1(u1_struct_0(A_31),k2_struct_0(A_31),B_32)) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_1),k2_struct_0(A_1),B_3),A_1)
      | ~ v4_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [B_43,A_44] :
      ( v3_pre_topc(B_43,A_44)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),B_43),A_44)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),B_43),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_struct_0(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4])).

tff(c_154,plain,(
    ! [C_45,A_46] :
      ( v3_pre_topc(C_45,A_46)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_46),k2_struct_0(A_46),C_45),A_46)
      | ~ l1_pre_topc(A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_struct_0(A_46)
      | ~ m1_subset_1(k2_struct_0(A_46),k1_zfmisc_1(u1_struct_0(A_46))) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_217,plain,(
    ! [C_53,A_54] :
      ( v3_pre_topc(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_struct_0(A_54)
      | k2_pre_topc(A_54,k7_subset_1(u1_struct_0(A_54),k2_struct_0(A_54),C_53)) != k7_subset_1(u1_struct_0(A_54),k2_struct_0(A_54),C_53)
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54)
      | ~ m1_subset_1(k2_struct_0(A_54),k1_zfmisc_1(u1_struct_0(A_54))) ) ),
    inference(resolution,[status(thm)],[c_67,c_154])).

tff(c_225,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_217])).

tff(c_230,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34,c_18,c_225])).

tff(c_231,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_230])).

tff(c_232,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_236,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_239,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_239])).

tff(c_244,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_248,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_244])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_248])).

tff(c_254,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_263,plain,(
    ! [A_59,B_60] :
      ( k7_subset_1(u1_struct_0(A_59),k2_struct_0(A_59),k7_subset_1(u1_struct_0(A_59),k2_struct_0(A_59),B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v4_pre_topc(B_3,A_1)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_1),k2_struct_0(A_1),B_3),A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_301,plain,(
    ! [A_67,B_68] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_67),k2_struct_0(A_67),B_68),A_67)
      | ~ v3_pre_topc(B_68,A_67)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_67),k2_struct_0(A_67),B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_struct_0(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2])).

tff(c_310,plain,(
    ! [A_69,C_70] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_69),k2_struct_0(A_69),C_70),A_69)
      | ~ v3_pre_topc(C_70,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_struct_0(A_69)
      | ~ m1_subset_1(k2_struct_0(A_69),k1_zfmisc_1(u1_struct_0(A_69))) ) ),
    inference(resolution,[status(thm)],[c_8,c_301])).

tff(c_37,plain,(
    ! [A_21,B_22] :
      ( k2_pre_topc(A_21,B_22) = B_22
      | ~ v4_pre_topc(B_22,A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [A_21,B_6,C_7] :
      ( k2_pre_topc(A_21,k7_subset_1(u1_struct_0(A_21),B_6,C_7)) = k7_subset_1(u1_struct_0(A_21),B_6,C_7)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_21),B_6,C_7),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_21))) ) ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_340,plain,(
    ! [A_75,C_76] :
      ( k2_pre_topc(A_75,k7_subset_1(u1_struct_0(A_75),k2_struct_0(A_75),C_76)) = k7_subset_1(u1_struct_0(A_75),k2_struct_0(A_75),C_76)
      | ~ v3_pre_topc(C_76,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75)
      | ~ m1_subset_1(k2_struct_0(A_75),k1_zfmisc_1(u1_struct_0(A_75))) ) ),
    inference(resolution,[status(thm)],[c_310,c_48])).

tff(c_344,plain,(
    ! [A_77,C_78] :
      ( k2_pre_topc(A_77,k7_subset_1(u1_struct_0(A_77),k2_struct_0(A_77),C_78)) = k7_subset_1(u1_struct_0(A_77),k2_struct_0(A_77),C_78)
      | ~ v3_pre_topc(C_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_253,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_350,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_253])).

tff(c_360,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_254,c_350])).

tff(c_364,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_364])).

tff(c_369,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_424,plain,(
    ! [A_93,B_94] :
      ( k7_subset_1(u1_struct_0(A_93),k2_struct_0(A_93),k7_subset_1(u1_struct_0(A_93),k2_struct_0(A_93),B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_462,plain,(
    ! [A_101,B_102] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_101),k2_struct_0(A_101),B_102),A_101)
      | ~ v3_pre_topc(B_102,A_101)
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(A_101),k2_struct_0(A_101),B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_2])).

tff(c_471,plain,(
    ! [A_103,C_104] :
      ( v4_pre_topc(k7_subset_1(u1_struct_0(A_103),k2_struct_0(A_103),C_104),A_103)
      | ~ v3_pre_topc(C_104,A_103)
      | ~ l1_pre_topc(A_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_struct_0(A_103)
      | ~ m1_subset_1(k2_struct_0(A_103),k1_zfmisc_1(u1_struct_0(A_103))) ) ),
    inference(resolution,[status(thm)],[c_8,c_462])).

tff(c_373,plain,(
    ! [A_83,B_84] :
      ( k2_pre_topc(A_83,B_84) = B_84
      | ~ v4_pre_topc(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_384,plain,(
    ! [A_83,B_6,C_7] :
      ( k2_pre_topc(A_83,k7_subset_1(u1_struct_0(A_83),B_6,C_7)) = k7_subset_1(u1_struct_0(A_83),B_6,C_7)
      | ~ v4_pre_topc(k7_subset_1(u1_struct_0(A_83),B_6,C_7),A_83)
      | ~ l1_pre_topc(A_83)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_83))) ) ),
    inference(resolution,[status(thm)],[c_8,c_373])).

tff(c_501,plain,(
    ! [A_109,C_110] :
      ( k2_pre_topc(A_109,k7_subset_1(u1_struct_0(A_109),k2_struct_0(A_109),C_110)) = k7_subset_1(u1_struct_0(A_109),k2_struct_0(A_109),C_110)
      | ~ v3_pre_topc(C_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_struct_0(A_109)
      | ~ m1_subset_1(k2_struct_0(A_109),k1_zfmisc_1(u1_struct_0(A_109))) ) ),
    inference(resolution,[status(thm)],[c_471,c_384])).

tff(c_505,plain,(
    ! [A_111,C_112] :
      ( k2_pre_topc(A_111,k7_subset_1(u1_struct_0(A_111),k2_struct_0(A_111),C_112)) = k7_subset_1(u1_struct_0(A_111),k2_struct_0(A_111),C_112)
      | ~ v3_pre_topc(C_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_501])).

tff(c_370,plain,(
    ~ v2_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')
    | v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_391,plain,(
    k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2')) != k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_30])).

tff(c_511,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_391])).

tff(c_521,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_369,c_511])).

tff(c_549,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_521])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_549])).

%------------------------------------------------------------------------------
