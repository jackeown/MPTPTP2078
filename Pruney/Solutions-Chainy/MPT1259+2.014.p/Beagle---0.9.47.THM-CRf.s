%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 245 expanded)
%              Number of equality atoms :   50 (  62 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k2_tops_1(A,B)) = k2_tops_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_54,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_162,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,k2_tops_1(A_54,B_55)) = k2_tops_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_203,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,k2_tops_1(A_64,k2_tops_1(A_64,B_65))) = k2_tops_1(A_64,k2_tops_1(A_64,B_65))
      | ~ v2_pre_topc(A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_18,c_162])).

tff(c_207,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_203])).

tff(c_211,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_207])).

tff(c_149,plain,(
    ! [A_52,B_53] :
      ( k1_tops_1(A_52,k2_tops_1(A_52,k2_tops_1(A_52,B_53))) = k1_xboole_0
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_153,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_157,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_153])).

tff(c_121,plain,(
    ! [B_48,A_49] :
      ( v4_pre_topc(B_48,A_49)
      | k2_pre_topc(A_49,B_48) != B_48
      | ~ v2_pre_topc(A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_228,plain,(
    ! [A_68,B_69] :
      ( v4_pre_topc(k2_tops_1(A_68,B_69),A_68)
      | k2_pre_topc(A_68,k2_tops_1(A_68,B_69)) != k2_tops_1(A_68,B_69)
      | ~ v2_pre_topc(A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_233,plain,(
    ! [A_11,B_12] :
      ( v4_pre_topc(k2_tops_1(A_11,k2_tops_1(A_11,B_12)),A_11)
      | k2_pre_topc(A_11,k2_tops_1(A_11,k2_tops_1(A_11,B_12))) != k2_tops_1(A_11,k2_tops_1(A_11,B_12))
      | ~ v2_pre_topc(A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_228])).

tff(c_111,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k2_tops_1(A_46,B_47),B_47)
      | ~ v4_pre_topc(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k2_tops_1(A_66,k2_tops_1(A_66,B_67)),k2_tops_1(A_66,B_67))
      | ~ v4_pre_topc(k2_tops_1(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k2_tops_1(A_66,k2_tops_1(A_66,B_67)),k2_tops_1(A_66,B_67)) = k1_xboole_0
      | ~ v4_pre_topc(k2_tops_1(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_216,c_10])).

tff(c_96,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k2_tops_1(A_42,B_43),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( k7_subset_1(A_5,B_6,C_7) = k4_xboole_0(B_6,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_subset_1(u1_struct_0(A_58),k2_tops_1(A_58,B_59),C_60) = k4_xboole_0(k2_tops_1(A_58,B_59),C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_96,c_12])).

tff(c_282,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(u1_struct_0(A_74),k2_tops_1(A_74,k2_tops_1(A_74,B_75)),C_76) = k4_xboole_0(k2_tops_1(A_74,k2_tops_1(A_74,B_75)),C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_18,c_184])).

tff(c_133,plain,(
    ! [A_50,B_51] :
      ( k7_subset_1(u1_struct_0(A_50),B_51,k2_tops_1(A_50,B_51)) = k1_tops_1(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_138,plain,(
    ! [A_11,B_12] :
      ( k7_subset_1(u1_struct_0(A_11),k2_tops_1(A_11,B_12),k2_tops_1(A_11,k2_tops_1(A_11,B_12))) = k1_tops_1(A_11,k2_tops_1(A_11,B_12))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_354,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k2_tops_1(A_85,k2_tops_1(A_85,B_86)),k2_tops_1(A_85,k2_tops_1(A_85,k2_tops_1(A_85,B_86)))) = k1_tops_1(A_85,k2_tops_1(A_85,k2_tops_1(A_85,B_86)))
      | ~ m1_subset_1(k2_tops_1(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_138])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | k4_xboole_0(A_35,B_34) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_71,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_368,plain,(
    ! [A_87,B_88] :
      ( k2_tops_1(A_87,k2_tops_1(A_87,k2_tops_1(A_87,B_88))) = k2_tops_1(A_87,k2_tops_1(A_87,B_88))
      | k1_tops_1(A_87,k2_tops_1(A_87,k2_tops_1(A_87,B_88))) != k1_xboole_0
      | k4_xboole_0(k2_tops_1(A_87,k2_tops_1(A_87,k2_tops_1(A_87,B_88))),k2_tops_1(A_87,k2_tops_1(A_87,B_88))) != k1_xboole_0
      | ~ m1_subset_1(k2_tops_1(A_87,B_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_71])).

tff(c_374,plain,(
    ! [A_89,B_90] :
      ( k2_tops_1(A_89,k2_tops_1(A_89,k2_tops_1(A_89,B_90))) = k2_tops_1(A_89,k2_tops_1(A_89,B_90))
      | k1_tops_1(A_89,k2_tops_1(A_89,k2_tops_1(A_89,B_90))) != k1_xboole_0
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v4_pre_topc(k2_tops_1(A_89,k2_tops_1(A_89,B_90)),A_89)
      | ~ m1_subset_1(k2_tops_1(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_368])).

tff(c_378,plain,(
    ! [A_91,B_92] :
      ( k2_tops_1(A_91,k2_tops_1(A_91,k2_tops_1(A_91,B_92))) = k2_tops_1(A_91,k2_tops_1(A_91,B_92))
      | k1_tops_1(A_91,k2_tops_1(A_91,k2_tops_1(A_91,B_92))) != k1_xboole_0
      | ~ m1_subset_1(k2_tops_1(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | k2_pre_topc(A_91,k2_tops_1(A_91,k2_tops_1(A_91,B_92))) != k2_tops_1(A_91,k2_tops_1(A_91,B_92))
      | ~ v2_pre_topc(A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_233,c_374])).

tff(c_382,plain,(
    ! [A_93,B_94] :
      ( k2_tops_1(A_93,k2_tops_1(A_93,k2_tops_1(A_93,B_94))) = k2_tops_1(A_93,k2_tops_1(A_93,B_94))
      | k1_tops_1(A_93,k2_tops_1(A_93,k2_tops_1(A_93,B_94))) != k1_xboole_0
      | k2_pre_topc(A_93,k2_tops_1(A_93,k2_tops_1(A_93,B_94))) != k2_tops_1(A_93,k2_tops_1(A_93,B_94))
      | ~ v2_pre_topc(A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_18,c_378])).

tff(c_386,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k1_xboole_0
    | k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_382])).

tff(c_390,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_211,c_157,c_386])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:29:59 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.56/1.34  
% 2.56/1.34  %Foreground sorts:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Background operators:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Foreground operators:
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.56/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.56/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.34  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.56/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.56/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.34  
% 2.56/1.36  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 2.56/1.36  tff(f_60, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.56/1.36  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k2_tops_1(A, B)) = k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l79_tops_1)).
% 2.56/1.36  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 2.56/1.36  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.56/1.36  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.56/1.36  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.56/1.36  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.56/1.36  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 2.56/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.36  tff(c_28, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.56/1.36  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.56/1.36  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.56/1.36  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.56/1.36  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k2_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.36  tff(c_162, plain, (![A_54, B_55]: (k2_pre_topc(A_54, k2_tops_1(A_54, B_55))=k2_tops_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.56/1.36  tff(c_203, plain, (![A_64, B_65]: (k2_pre_topc(A_64, k2_tops_1(A_64, k2_tops_1(A_64, B_65)))=k2_tops_1(A_64, k2_tops_1(A_64, B_65)) | ~v2_pre_topc(A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_18, c_162])).
% 2.56/1.36  tff(c_207, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_203])).
% 2.56/1.36  tff(c_211, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_207])).
% 2.56/1.36  tff(c_149, plain, (![A_52, B_53]: (k1_tops_1(A_52, k2_tops_1(A_52, k2_tops_1(A_52, B_53)))=k1_xboole_0 | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.36  tff(c_153, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.56/1.36  tff(c_157, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_153])).
% 2.56/1.36  tff(c_121, plain, (![B_48, A_49]: (v4_pre_topc(B_48, A_49) | k2_pre_topc(A_49, B_48)!=B_48 | ~v2_pre_topc(A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.56/1.36  tff(c_228, plain, (![A_68, B_69]: (v4_pre_topc(k2_tops_1(A_68, B_69), A_68) | k2_pre_topc(A_68, k2_tops_1(A_68, B_69))!=k2_tops_1(A_68, B_69) | ~v2_pre_topc(A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_18, c_121])).
% 2.56/1.36  tff(c_233, plain, (![A_11, B_12]: (v4_pre_topc(k2_tops_1(A_11, k2_tops_1(A_11, B_12)), A_11) | k2_pre_topc(A_11, k2_tops_1(A_11, k2_tops_1(A_11, B_12)))!=k2_tops_1(A_11, k2_tops_1(A_11, B_12)) | ~v2_pre_topc(A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_18, c_228])).
% 2.56/1.36  tff(c_111, plain, (![A_46, B_47]: (r1_tarski(k2_tops_1(A_46, B_47), B_47) | ~v4_pre_topc(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.36  tff(c_216, plain, (![A_66, B_67]: (r1_tarski(k2_tops_1(A_66, k2_tops_1(A_66, B_67)), k2_tops_1(A_66, B_67)) | ~v4_pre_topc(k2_tops_1(A_66, B_67), A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_18, c_111])).
% 2.56/1.36  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.36  tff(c_227, plain, (![A_66, B_67]: (k4_xboole_0(k2_tops_1(A_66, k2_tops_1(A_66, B_67)), k2_tops_1(A_66, B_67))=k1_xboole_0 | ~v4_pre_topc(k2_tops_1(A_66, B_67), A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_216, c_10])).
% 2.56/1.36  tff(c_96, plain, (![A_42, B_43]: (m1_subset_1(k2_tops_1(A_42, B_43), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.36  tff(c_12, plain, (![A_5, B_6, C_7]: (k7_subset_1(A_5, B_6, C_7)=k4_xboole_0(B_6, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.36  tff(c_184, plain, (![A_58, B_59, C_60]: (k7_subset_1(u1_struct_0(A_58), k2_tops_1(A_58, B_59), C_60)=k4_xboole_0(k2_tops_1(A_58, B_59), C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_96, c_12])).
% 2.56/1.36  tff(c_282, plain, (![A_74, B_75, C_76]: (k7_subset_1(u1_struct_0(A_74), k2_tops_1(A_74, k2_tops_1(A_74, B_75)), C_76)=k4_xboole_0(k2_tops_1(A_74, k2_tops_1(A_74, B_75)), C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_18, c_184])).
% 2.56/1.36  tff(c_133, plain, (![A_50, B_51]: (k7_subset_1(u1_struct_0(A_50), B_51, k2_tops_1(A_50, B_51))=k1_tops_1(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.36  tff(c_138, plain, (![A_11, B_12]: (k7_subset_1(u1_struct_0(A_11), k2_tops_1(A_11, B_12), k2_tops_1(A_11, k2_tops_1(A_11, B_12)))=k1_tops_1(A_11, k2_tops_1(A_11, B_12)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_18, c_133])).
% 2.56/1.36  tff(c_354, plain, (![A_85, B_86]: (k4_xboole_0(k2_tops_1(A_85, k2_tops_1(A_85, B_86)), k2_tops_1(A_85, k2_tops_1(A_85, k2_tops_1(A_85, B_86))))=k1_tops_1(A_85, k2_tops_1(A_85, k2_tops_1(A_85, B_86))) | ~m1_subset_1(k2_tops_1(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(superposition, [status(thm), theory('equality')], [c_282, c_138])).
% 2.56/1.36  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.36  tff(c_54, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.36  tff(c_64, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | k4_xboole_0(A_35, B_34)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_54])).
% 2.56/1.36  tff(c_71, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.56/1.36  tff(c_368, plain, (![A_87, B_88]: (k2_tops_1(A_87, k2_tops_1(A_87, k2_tops_1(A_87, B_88)))=k2_tops_1(A_87, k2_tops_1(A_87, B_88)) | k1_tops_1(A_87, k2_tops_1(A_87, k2_tops_1(A_87, B_88)))!=k1_xboole_0 | k4_xboole_0(k2_tops_1(A_87, k2_tops_1(A_87, k2_tops_1(A_87, B_88))), k2_tops_1(A_87, k2_tops_1(A_87, B_88)))!=k1_xboole_0 | ~m1_subset_1(k2_tops_1(A_87, B_88), k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_354, c_71])).
% 2.56/1.36  tff(c_374, plain, (![A_89, B_90]: (k2_tops_1(A_89, k2_tops_1(A_89, k2_tops_1(A_89, B_90)))=k2_tops_1(A_89, k2_tops_1(A_89, B_90)) | k1_tops_1(A_89, k2_tops_1(A_89, k2_tops_1(A_89, B_90)))!=k1_xboole_0 | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~v4_pre_topc(k2_tops_1(A_89, k2_tops_1(A_89, B_90)), A_89) | ~m1_subset_1(k2_tops_1(A_89, B_90), k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(superposition, [status(thm), theory('equality')], [c_227, c_368])).
% 2.56/1.36  tff(c_378, plain, (![A_91, B_92]: (k2_tops_1(A_91, k2_tops_1(A_91, k2_tops_1(A_91, B_92)))=k2_tops_1(A_91, k2_tops_1(A_91, B_92)) | k1_tops_1(A_91, k2_tops_1(A_91, k2_tops_1(A_91, B_92)))!=k1_xboole_0 | ~m1_subset_1(k2_tops_1(A_91, B_92), k1_zfmisc_1(u1_struct_0(A_91))) | k2_pre_topc(A_91, k2_tops_1(A_91, k2_tops_1(A_91, B_92)))!=k2_tops_1(A_91, k2_tops_1(A_91, B_92)) | ~v2_pre_topc(A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_233, c_374])).
% 2.56/1.36  tff(c_382, plain, (![A_93, B_94]: (k2_tops_1(A_93, k2_tops_1(A_93, k2_tops_1(A_93, B_94)))=k2_tops_1(A_93, k2_tops_1(A_93, B_94)) | k1_tops_1(A_93, k2_tops_1(A_93, k2_tops_1(A_93, B_94)))!=k1_xboole_0 | k2_pre_topc(A_93, k2_tops_1(A_93, k2_tops_1(A_93, B_94)))!=k2_tops_1(A_93, k2_tops_1(A_93, B_94)) | ~v2_pre_topc(A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_18, c_378])).
% 2.56/1.36  tff(c_386, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k1_xboole_0 | k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_382])).
% 2.56/1.36  tff(c_390, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_211, c_157, c_386])).
% 2.56/1.36  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_390])).
% 2.56/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  Inference rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Ref     : 0
% 2.56/1.36  #Sup     : 82
% 2.56/1.36  #Fact    : 0
% 2.56/1.36  #Define  : 0
% 2.56/1.36  #Split   : 4
% 2.56/1.36  #Chain   : 0
% 2.56/1.36  #Close   : 0
% 2.56/1.36  
% 2.56/1.36  Ordering : KBO
% 2.56/1.36  
% 2.56/1.36  Simplification rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Subsume      : 8
% 2.56/1.36  #Demod        : 45
% 2.56/1.36  #Tautology    : 39
% 2.56/1.36  #SimpNegUnit  : 2
% 2.56/1.36  #BackRed      : 0
% 2.56/1.36  
% 2.56/1.36  #Partial instantiations: 0
% 2.56/1.36  #Strategies tried      : 1
% 2.56/1.36  
% 2.56/1.36  Timing (in seconds)
% 2.56/1.36  ----------------------
% 2.56/1.36  Preprocessing        : 0.33
% 2.56/1.36  Parsing              : 0.18
% 2.56/1.36  CNF conversion       : 0.02
% 2.56/1.36  Main loop            : 0.29
% 2.56/1.36  Inferencing          : 0.11
% 2.56/1.36  Reduction            : 0.08
% 2.80/1.36  Demodulation         : 0.06
% 2.80/1.36  BG Simplification    : 0.02
% 2.80/1.36  Subsumption          : 0.06
% 2.80/1.36  Abstraction          : 0.02
% 2.80/1.37  MUC search           : 0.00
% 2.80/1.37  Cooper               : 0.00
% 2.80/1.37  Total                : 0.65
% 2.80/1.37  Index Insertion      : 0.00
% 2.80/1.37  Index Deletion       : 0.00
% 2.80/1.37  Index Matching       : 0.00
% 2.80/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
