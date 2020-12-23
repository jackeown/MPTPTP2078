%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 172 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 354 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_845,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_859,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_845])).

tff(c_40,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_860,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_40])).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_82])).

tff(c_216,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_225,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_226,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_40])).

tff(c_137,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_146,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_290,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_304,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_290])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [A_82,C_83,B_84] :
      ( m1_subset_1(A_82,C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_212,plain,(
    ! [A_86,B_87,A_88] :
      ( m1_subset_1(A_86,B_87)
      | ~ r2_hidden(A_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_204])).

tff(c_231,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_1'(A_92),B_93)
      | ~ r1_tarski(A_92,B_93)
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_2,c_212])).

tff(c_65,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_50,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_203,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_260,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_203])).

tff(c_265,plain,(
    ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_305,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_265])).

tff(c_314,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_305])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_146,c_314])).

tff(c_319,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_373,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_384,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_373])).

tff(c_388,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_384])).

tff(c_28,plain,(
    ! [A_21] :
      ( k7_relat_1(A_21,k1_relat_1(A_21)) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_158,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(k7_relat_1(B_76,A_77)) = k9_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_173,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_158])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [B_101,A_102] :
      ( k9_relat_1(B_101,A_102) != k1_xboole_0
      | ~ r1_tarski(A_102,k1_relat_1(B_101))
      | k1_xboole_0 = A_102
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_369,plain,(
    ! [B_104] :
      ( k9_relat_1(B_104,k1_relat_1(B_104)) != k1_xboole_0
      | k1_relat_1(B_104) = k1_xboole_0
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_8,c_349])).

tff(c_662,plain,(
    ! [A_147] :
      ( k2_relat_1(A_147) != k1_xboole_0
      | k1_relat_1(A_147) = k1_xboole_0
      | ~ v1_relat_1(A_147)
      | ~ v1_relat_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_369])).

tff(c_668,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_662])).

tff(c_675,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_388,c_668])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_675])).

tff(c_678,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_769,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_780,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_769])).

tff(c_784,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_780])).

tff(c_705,plain,(
    ! [B_156,A_157] :
      ( k9_relat_1(B_156,A_157) != k1_xboole_0
      | ~ r1_tarski(A_157,k1_relat_1(B_156))
      | k1_xboole_0 = A_157
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_750,plain,(
    ! [B_161] :
      ( k9_relat_1(B_161,k1_relat_1(B_161)) != k1_xboole_0
      | k1_relat_1(B_161) = k1_xboole_0
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_8,c_705])).

tff(c_1055,plain,(
    ! [A_204] :
      ( k2_relat_1(A_204) != k1_xboole_0
      | k1_relat_1(A_204) = k1_xboole_0
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_750])).

tff(c_1061,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1055])).

tff(c_1068,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_784,c_1061])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_860,c_1068])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.43  
% 2.95/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.95/1.43  
% 2.95/1.43  %Foreground sorts:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Background operators:
% 2.95/1.43  
% 2.95/1.43  
% 2.95/1.43  %Foreground operators:
% 2.95/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.95/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.95/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.95/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.95/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.43  
% 3.24/1.45  tff(f_117, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.24/1.45  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.45  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.24/1.45  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.24/1.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.45  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.24/1.45  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.24/1.45  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.24/1.45  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.24/1.45  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.24/1.45  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.24/1.45  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.24/1.45  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.45  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 3.24/1.45  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.24/1.45  tff(c_845, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.45  tff(c_859, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_845])).
% 3.24/1.45  tff(c_40, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.24/1.45  tff(c_860, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_859, c_40])).
% 3.24/1.45  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.24/1.45  tff(c_76, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.45  tff(c_82, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_76])).
% 3.24/1.45  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_82])).
% 3.24/1.45  tff(c_216, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.45  tff(c_225, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_216])).
% 3.24/1.45  tff(c_226, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_225, c_40])).
% 3.24/1.45  tff(c_137, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.45  tff(c_146, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_137])).
% 3.24/1.45  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.45  tff(c_290, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.45  tff(c_304, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_290])).
% 3.24/1.45  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.45  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.45  tff(c_204, plain, (![A_82, C_83, B_84]: (m1_subset_1(A_82, C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.45  tff(c_212, plain, (![A_86, B_87, A_88]: (m1_subset_1(A_86, B_87) | ~r2_hidden(A_86, A_88) | ~r1_tarski(A_88, B_87))), inference(resolution, [status(thm)], [c_12, c_204])).
% 3.24/1.45  tff(c_231, plain, (![A_92, B_93]: (m1_subset_1('#skF_1'(A_92), B_93) | ~r1_tarski(A_92, B_93) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_2, c_212])).
% 3.24/1.45  tff(c_65, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_50, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.24/1.45  tff(c_70, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_65])).
% 3.24/1.45  tff(c_203, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 3.24/1.45  tff(c_260, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_231, c_203])).
% 3.24/1.45  tff(c_265, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_260])).
% 3.24/1.45  tff(c_305, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_265])).
% 3.24/1.45  tff(c_314, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_305])).
% 3.24/1.45  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_146, c_314])).
% 3.24/1.45  tff(c_319, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_260])).
% 3.24/1.45  tff(c_373, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.45  tff(c_384, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_373])).
% 3.24/1.45  tff(c_388, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_319, c_384])).
% 3.24/1.45  tff(c_28, plain, (![A_21]: (k7_relat_1(A_21, k1_relat_1(A_21))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.24/1.45  tff(c_158, plain, (![B_76, A_77]: (k2_relat_1(k7_relat_1(B_76, A_77))=k9_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.45  tff(c_173, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_28, c_158])).
% 3.24/1.45  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.45  tff(c_349, plain, (![B_101, A_102]: (k9_relat_1(B_101, A_102)!=k1_xboole_0 | ~r1_tarski(A_102, k1_relat_1(B_101)) | k1_xboole_0=A_102 | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.24/1.45  tff(c_369, plain, (![B_104]: (k9_relat_1(B_104, k1_relat_1(B_104))!=k1_xboole_0 | k1_relat_1(B_104)=k1_xboole_0 | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_8, c_349])).
% 3.24/1.45  tff(c_662, plain, (![A_147]: (k2_relat_1(A_147)!=k1_xboole_0 | k1_relat_1(A_147)=k1_xboole_0 | ~v1_relat_1(A_147) | ~v1_relat_1(A_147) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_173, c_369])).
% 3.24/1.45  tff(c_668, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_662])).
% 3.24/1.45  tff(c_675, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_388, c_668])).
% 3.24/1.45  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_675])).
% 3.24/1.45  tff(c_678, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 3.24/1.45  tff(c_769, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.45  tff(c_780, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_769])).
% 3.24/1.45  tff(c_784, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_678, c_780])).
% 3.24/1.45  tff(c_705, plain, (![B_156, A_157]: (k9_relat_1(B_156, A_157)!=k1_xboole_0 | ~r1_tarski(A_157, k1_relat_1(B_156)) | k1_xboole_0=A_157 | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.24/1.45  tff(c_750, plain, (![B_161]: (k9_relat_1(B_161, k1_relat_1(B_161))!=k1_xboole_0 | k1_relat_1(B_161)=k1_xboole_0 | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_8, c_705])).
% 3.24/1.45  tff(c_1055, plain, (![A_204]: (k2_relat_1(A_204)!=k1_xboole_0 | k1_relat_1(A_204)=k1_xboole_0 | ~v1_relat_1(A_204) | ~v1_relat_1(A_204) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_173, c_750])).
% 3.24/1.45  tff(c_1061, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_1055])).
% 3.24/1.45  tff(c_1068, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_784, c_1061])).
% 3.24/1.45  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_860, c_1068])).
% 3.24/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.45  
% 3.24/1.45  Inference rules
% 3.24/1.45  ----------------------
% 3.24/1.45  #Ref     : 0
% 3.24/1.45  #Sup     : 207
% 3.24/1.45  #Fact    : 0
% 3.24/1.45  #Define  : 0
% 3.24/1.45  #Split   : 8
% 3.24/1.45  #Chain   : 0
% 3.24/1.45  #Close   : 0
% 3.24/1.45  
% 3.24/1.45  Ordering : KBO
% 3.24/1.45  
% 3.24/1.45  Simplification rules
% 3.24/1.45  ----------------------
% 3.24/1.45  #Subsume      : 14
% 3.24/1.45  #Demod        : 87
% 3.24/1.45  #Tautology    : 65
% 3.24/1.45  #SimpNegUnit  : 2
% 3.24/1.45  #BackRed      : 8
% 3.24/1.45  
% 3.24/1.45  #Partial instantiations: 0
% 3.24/1.45  #Strategies tried      : 1
% 3.24/1.45  
% 3.24/1.45  Timing (in seconds)
% 3.24/1.45  ----------------------
% 3.24/1.45  Preprocessing        : 0.31
% 3.24/1.45  Parsing              : 0.16
% 3.24/1.45  CNF conversion       : 0.02
% 3.24/1.45  Main loop            : 0.39
% 3.24/1.45  Inferencing          : 0.15
% 3.24/1.46  Reduction            : 0.11
% 3.24/1.46  Demodulation         : 0.08
% 3.24/1.46  BG Simplification    : 0.02
% 3.24/1.46  Subsumption          : 0.07
% 3.24/1.46  Abstraction          : 0.02
% 3.24/1.46  MUC search           : 0.00
% 3.24/1.46  Cooper               : 0.00
% 3.24/1.46  Total                : 0.73
% 3.24/1.46  Index Insertion      : 0.00
% 3.24/1.46  Index Deletion       : 0.00
% 3.24/1.46  Index Matching       : 0.00
% 3.24/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
