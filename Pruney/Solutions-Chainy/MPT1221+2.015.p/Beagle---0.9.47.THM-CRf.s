%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 161 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 437 expanded)
%              Number of equality atoms :   20 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( k2_struct_0(A) = k4_subset_1(u1_struct_0(A),B,C)
                  & r1_xboole_0(B,C) )
               => C = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_28,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_37,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34])).

tff(c_18,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_47,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_1'(A_44,B_45,C_46),B_45)
      | r1_tarski(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_63,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_53])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [B_4,A_3,C_6] :
      ( r1_xboole_0(B_4,k3_subset_1(A_3,C_6))
      | ~ r1_tarski(B_4,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_18,B_20] :
      ( k4_subset_1(u1_struct_0(A_18),B_20,k3_subset_1(u1_struct_0(A_18),B_20)) = k2_struct_0(A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(u1_struct_0(A_60),k2_struct_0(A_60),B_61) = C_62
      | ~ r1_xboole_0(B_61,C_62)
      | k4_subset_1(u1_struct_0(A_60),B_61,C_62) != k2_struct_0(A_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    ! [A_63,B_64] :
      ( k7_subset_1(u1_struct_0(A_63),k2_struct_0(A_63),B_64) = k3_subset_1(u1_struct_0(A_63),B_64)
      | ~ r1_xboole_0(B_64,k3_subset_1(u1_struct_0(A_63),B_64))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_63),B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_struct_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_90,plain,(
    ! [A_65,C_66] :
      ( k7_subset_1(u1_struct_0(A_65),k2_struct_0(A_65),C_66) = k3_subset_1(u1_struct_0(A_65),C_66)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_65),C_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_struct_0(A_65)
      | ~ r1_tarski(C_66,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_65))) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_95,plain,(
    ! [A_67,B_68] :
      ( k7_subset_1(u1_struct_0(A_67),k2_struct_0(A_67),B_68) = k3_subset_1(u1_struct_0(A_67),B_68)
      | ~ l1_struct_0(A_67)
      | ~ r1_tarski(B_68,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67))) ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_105,plain,(
    ! [A_69] :
      ( k7_subset_1(u1_struct_0(A_69),k2_struct_0(A_69),'#skF_3') = k3_subset_1(u1_struct_0(A_69),'#skF_3')
      | ~ l1_struct_0(A_69)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_69))) ) ),
    inference(resolution,[status(thm)],[c_63,c_95])).

tff(c_108,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_109,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_117,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_117])).

tff(c_122,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_14,plain,(
    ! [B_16,A_14] :
      ( v4_pre_topc(B_16,A_14)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_14),k2_struct_0(A_14),B_16),A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_130,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_14])).

tff(c_136,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_37,c_130])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_136])).

tff(c_139,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_140,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_154,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_1'(A_84,B_85,C_86),B_85)
      | r1_tarski(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_160,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_154,c_8])).

tff(c_166,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_188,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(u1_struct_0(A_100),k2_struct_0(A_100),B_101) = C_102
      | ~ r1_xboole_0(B_101,C_102)
      | k4_subset_1(u1_struct_0(A_100),B_101,C_102) != k2_struct_0(A_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_193,plain,(
    ! [A_106,B_107] :
      ( k7_subset_1(u1_struct_0(A_106),k2_struct_0(A_106),B_107) = k3_subset_1(u1_struct_0(A_106),B_107)
      | ~ r1_xboole_0(B_107,k3_subset_1(u1_struct_0(A_106),B_107))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_106),B_107),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_struct_0(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_198,plain,(
    ! [A_108,C_109] :
      ( k7_subset_1(u1_struct_0(A_108),k2_struct_0(A_108),C_109) = k3_subset_1(u1_struct_0(A_108),C_109)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_108),C_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_struct_0(A_108)
      | ~ r1_tarski(C_109,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108))) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_203,plain,(
    ! [A_110,B_111] :
      ( k7_subset_1(u1_struct_0(A_110),k2_struct_0(A_110),B_111) = k3_subset_1(u1_struct_0(A_110),B_111)
      | ~ l1_struct_0(A_110)
      | ~ r1_tarski(B_111,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110))) ) ),
    inference(resolution,[status(thm)],[c_2,c_198])).

tff(c_213,plain,(
    ! [A_112] :
      ( k7_subset_1(u1_struct_0(A_112),k2_struct_0(A_112),'#skF_3') = k3_subset_1(u1_struct_0(A_112),'#skF_3')
      | ~ l1_struct_0(A_112)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_112))) ) ),
    inference(resolution,[status(thm)],[c_166,c_203])).

tff(c_216,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_213])).

tff(c_222,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_225,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_225])).

tff(c_230,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_14),k2_struct_0(A_14),B_16),A_14)
      | ~ v4_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_235,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_16])).

tff(c_242,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_140,c_235])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:40:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.38  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.45/1.38  
% 2.45/1.38  %Foreground sorts:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Background operators:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Foreground operators:
% 2.45/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.45/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.45/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.45/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.45/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.45/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.45/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.45/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.38  
% 2.45/1.39  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.45/1.39  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.45/1.39  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.45/1.39  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.45/1.39  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.45/1.39  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.45/1.39  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((k2_struct_0(A) = k4_subset_1(u1_struct_0(A), B, C)) & r1_xboole_0(B, C)) => (C = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_pre_topc)).
% 2.45/1.39  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.45/1.39  tff(c_28, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.45/1.39  tff(c_36, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 2.45/1.39  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.45/1.39  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.45/1.39  tff(c_34, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.45/1.39  tff(c_37, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_34])).
% 2.45/1.39  tff(c_18, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.39  tff(c_47, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_1'(A_44, B_45, C_46), B_45) | r1_tarski(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.39  tff(c_8, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.39  tff(c_53, plain, (![B_47, A_48]: (r1_tarski(B_47, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_47, c_8])).
% 2.45/1.39  tff(c_63, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_53])).
% 2.45/1.39  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.39  tff(c_4, plain, (![B_4, A_3, C_6]: (r1_xboole_0(B_4, k3_subset_1(A_3, C_6)) | ~r1_tarski(B_4, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.45/1.39  tff(c_20, plain, (![A_18, B_20]: (k4_subset_1(u1_struct_0(A_18), B_20, k3_subset_1(u1_struct_0(A_18), B_20))=k2_struct_0(A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.39  tff(c_81, plain, (![A_60, B_61, C_62]: (k7_subset_1(u1_struct_0(A_60), k2_struct_0(A_60), B_61)=C_62 | ~r1_xboole_0(B_61, C_62) | k4_subset_1(u1_struct_0(A_60), B_61, C_62)!=k2_struct_0(A_60) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.39  tff(c_85, plain, (![A_63, B_64]: (k7_subset_1(u1_struct_0(A_63), k2_struct_0(A_63), B_64)=k3_subset_1(u1_struct_0(A_63), B_64) | ~r1_xboole_0(B_64, k3_subset_1(u1_struct_0(A_63), B_64)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_63), B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_struct_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_20, c_81])).
% 2.45/1.39  tff(c_90, plain, (![A_65, C_66]: (k7_subset_1(u1_struct_0(A_65), k2_struct_0(A_65), C_66)=k3_subset_1(u1_struct_0(A_65), C_66) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_65), C_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_struct_0(A_65) | ~r1_tarski(C_66, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_65))))), inference(resolution, [status(thm)], [c_4, c_85])).
% 2.45/1.39  tff(c_95, plain, (![A_67, B_68]: (k7_subset_1(u1_struct_0(A_67), k2_struct_0(A_67), B_68)=k3_subset_1(u1_struct_0(A_67), B_68) | ~l1_struct_0(A_67) | ~r1_tarski(B_68, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))))), inference(resolution, [status(thm)], [c_2, c_90])).
% 2.45/1.39  tff(c_105, plain, (![A_69]: (k7_subset_1(u1_struct_0(A_69), k2_struct_0(A_69), '#skF_3')=k3_subset_1(u1_struct_0(A_69), '#skF_3') | ~l1_struct_0(A_69) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_69))))), inference(resolution, [status(thm)], [c_63, c_95])).
% 2.45/1.39  tff(c_108, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_105])).
% 2.45/1.39  tff(c_109, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_108])).
% 2.45/1.39  tff(c_117, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_109])).
% 2.45/1.39  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_117])).
% 2.45/1.39  tff(c_122, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_108])).
% 2.45/1.39  tff(c_14, plain, (![B_16, A_14]: (v4_pre_topc(B_16, A_14) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_14), k2_struct_0(A_14), B_16), A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.39  tff(c_130, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_14])).
% 2.45/1.39  tff(c_136, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_37, c_130])).
% 2.45/1.39  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_136])).
% 2.45/1.39  tff(c_139, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.45/1.39  tff(c_140, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.45/1.39  tff(c_154, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_1'(A_84, B_85, C_86), B_85) | r1_tarski(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.39  tff(c_160, plain, (![B_87, A_88]: (r1_tarski(B_87, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_154, c_8])).
% 2.45/1.39  tff(c_166, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_160])).
% 2.45/1.39  tff(c_188, plain, (![A_100, B_101, C_102]: (k7_subset_1(u1_struct_0(A_100), k2_struct_0(A_100), B_101)=C_102 | ~r1_xboole_0(B_101, C_102) | k4_subset_1(u1_struct_0(A_100), B_101, C_102)!=k2_struct_0(A_100) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.39  tff(c_193, plain, (![A_106, B_107]: (k7_subset_1(u1_struct_0(A_106), k2_struct_0(A_106), B_107)=k3_subset_1(u1_struct_0(A_106), B_107) | ~r1_xboole_0(B_107, k3_subset_1(u1_struct_0(A_106), B_107)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_106), B_107), k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_struct_0(A_106))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 2.45/1.39  tff(c_198, plain, (![A_108, C_109]: (k7_subset_1(u1_struct_0(A_108), k2_struct_0(A_108), C_109)=k3_subset_1(u1_struct_0(A_108), C_109) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_108), C_109), k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_struct_0(A_108) | ~r1_tarski(C_109, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))))), inference(resolution, [status(thm)], [c_4, c_193])).
% 2.45/1.39  tff(c_203, plain, (![A_110, B_111]: (k7_subset_1(u1_struct_0(A_110), k2_struct_0(A_110), B_111)=k3_subset_1(u1_struct_0(A_110), B_111) | ~l1_struct_0(A_110) | ~r1_tarski(B_111, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))))), inference(resolution, [status(thm)], [c_2, c_198])).
% 2.45/1.39  tff(c_213, plain, (![A_112]: (k7_subset_1(u1_struct_0(A_112), k2_struct_0(A_112), '#skF_3')=k3_subset_1(u1_struct_0(A_112), '#skF_3') | ~l1_struct_0(A_112) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_112))))), inference(resolution, [status(thm)], [c_166, c_203])).
% 2.45/1.39  tff(c_216, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_213])).
% 2.45/1.39  tff(c_222, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_216])).
% 2.45/1.39  tff(c_225, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_222])).
% 2.45/1.39  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_225])).
% 2.45/1.39  tff(c_230, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_216])).
% 2.45/1.39  tff(c_16, plain, (![A_14, B_16]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_14), k2_struct_0(A_14), B_16), A_14) | ~v4_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.39  tff(c_235, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_230, c_16])).
% 2.45/1.39  tff(c_242, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_140, c_235])).
% 2.45/1.39  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_242])).
% 2.45/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  Inference rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Ref     : 0
% 2.45/1.39  #Sup     : 42
% 2.45/1.39  #Fact    : 0
% 2.45/1.39  #Define  : 0
% 2.45/1.39  #Split   : 4
% 2.45/1.39  #Chain   : 0
% 2.45/1.39  #Close   : 0
% 2.45/1.39  
% 2.45/1.39  Ordering : KBO
% 2.45/1.39  
% 2.45/1.39  Simplification rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Subsume      : 4
% 2.45/1.39  #Demod        : 12
% 2.45/1.39  #Tautology    : 13
% 2.45/1.39  #SimpNegUnit  : 4
% 2.45/1.39  #BackRed      : 0
% 2.45/1.39  
% 2.45/1.39  #Partial instantiations: 0
% 2.45/1.39  #Strategies tried      : 1
% 2.45/1.39  
% 2.45/1.39  Timing (in seconds)
% 2.45/1.39  ----------------------
% 2.45/1.40  Preprocessing        : 0.33
% 2.45/1.40  Parsing              : 0.18
% 2.45/1.40  CNF conversion       : 0.03
% 2.45/1.40  Main loop            : 0.24
% 2.45/1.40  Inferencing          : 0.11
% 2.45/1.40  Reduction            : 0.06
% 2.45/1.40  Demodulation         : 0.03
% 2.45/1.40  BG Simplification    : 0.02
% 2.45/1.40  Subsumption          : 0.04
% 2.45/1.40  Abstraction          : 0.01
% 2.45/1.40  MUC search           : 0.00
% 2.45/1.40  Cooper               : 0.00
% 2.45/1.40  Total                : 0.60
% 2.45/1.40  Index Insertion      : 0.00
% 2.45/1.40  Index Deletion       : 0.00
% 2.45/1.40  Index Matching       : 0.00
% 2.45/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
