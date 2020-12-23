%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 210 expanded)
%              Number of leaves         :   47 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 437 expanded)
%              Number of equality atoms :   59 ( 105 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2502,plain,(
    ! [A_354,B_355,C_356] :
      ( k1_relset_1(A_354,B_355,C_356) = k1_relat_1(C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2516,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_2502])).

tff(c_68,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2517,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_68])).

tff(c_50,plain,(
    ! [A_39,B_40] : v1_relat_1(k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_126,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_136,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_126])).

tff(c_141,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_136])).

tff(c_712,plain,(
    ! [A_180,B_181,C_182] :
      ( k1_relset_1(A_180,B_181,C_182) = k1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_732,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_712])).

tff(c_733,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_68])).

tff(c_195,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_209,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_195])).

tff(c_48,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_24] : k3_tarski(k1_zfmisc_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_375,plain,(
    ! [C_125,A_126,D_127] :
      ( r2_hidden(C_125,k3_tarski(A_126))
      | ~ r2_hidden(D_127,A_126)
      | ~ r2_hidden(C_125,D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1051,plain,(
    ! [C_224,B_225,A_226] :
      ( r2_hidden(C_224,k3_tarski(B_225))
      | ~ r2_hidden(C_224,A_226)
      | v1_xboole_0(B_225)
      | ~ m1_subset_1(A_226,B_225) ) ),
    inference(resolution,[status(thm)],[c_34,c_375])).

tff(c_1114,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_1'(A_231),k3_tarski(B_232))
      | v1_xboole_0(B_232)
      | ~ m1_subset_1(A_231,B_232)
      | k1_xboole_0 = A_231 ) ),
    inference(resolution,[status(thm)],[c_2,c_1051])).

tff(c_1124,plain,(
    ! [A_231,A_24] :
      ( r2_hidden('#skF_1'(A_231),A_24)
      | v1_xboole_0(k1_zfmisc_1(A_24))
      | ~ m1_subset_1(A_231,k1_zfmisc_1(A_24))
      | k1_xboole_0 = A_231 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1114])).

tff(c_1129,plain,(
    ! [A_233,A_234] :
      ( r2_hidden('#skF_1'(A_233),A_234)
      | ~ m1_subset_1(A_233,k1_zfmisc_1(A_234))
      | k1_xboole_0 = A_233 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1124])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1166,plain,(
    ! [A_237,A_238] :
      ( m1_subset_1('#skF_1'(A_237),A_238)
      | ~ m1_subset_1(A_237,k1_zfmisc_1(A_238))
      | k1_xboole_0 = A_237 ) ),
    inference(resolution,[status(thm)],[c_1129,c_32])).

tff(c_490,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_relset_1(A_150,B_151,C_152) = k2_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_504,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_490])).

tff(c_90,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_1'(A_76),A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [D_67] :
      ( ~ r2_hidden(D_67,k2_relset_1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1(D_67,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_98,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7')
    | k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_66])).

tff(c_153,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_507,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_153])).

tff(c_1200,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1166,c_507])).

tff(c_1206,plain,(
    ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1200])).

tff(c_1210,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_1206])).

tff(c_1240,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1210])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_209,c_1240])).

tff(c_1245,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1200])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_255,plain,(
    ! [B_109,A_110] :
      ( v4_relat_1(B_109,A_110)
      | ~ r1_tarski(k1_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_260,plain,(
    ! [B_109] :
      ( v4_relat_1(B_109,k1_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_296,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = B_116
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_332,plain,(
    ! [B_119] :
      ( k7_relat_1(B_119,k1_relat_1(B_119)) = B_119
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_260,c_296])).

tff(c_52,plain,(
    ! [B_42,A_41] :
      ( k2_relat_1(k7_relat_1(B_42,A_41)) = k9_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_338,plain,(
    ! [B_119] :
      ( k9_relat_1(B_119,k1_relat_1(B_119)) = k2_relat_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_52])).

tff(c_572,plain,(
    ! [B_161,A_162] :
      ( k9_relat_1(B_161,A_162) != k1_xboole_0
      | ~ r1_tarski(A_162,k1_relat_1(B_161))
      | k1_xboole_0 = A_162
      | ~ v1_relat_1(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_593,plain,(
    ! [B_163] :
      ( k9_relat_1(B_163,k1_relat_1(B_163)) != k1_xboole_0
      | k1_relat_1(B_163) = k1_xboole_0
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_8,c_572])).

tff(c_2011,plain,(
    ! [B_279] :
      ( k2_relat_1(B_279) != k1_xboole_0
      | k1_relat_1(B_279) = k1_xboole_0
      | ~ v1_relat_1(B_279)
      | ~ v1_relat_1(B_279)
      | ~ v1_relat_1(B_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_593])).

tff(c_2021,plain,
    ( k2_relat_1('#skF_8') != k1_xboole_0
    | k1_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_141,c_2011])).

tff(c_2030,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1245,c_2021])).

tff(c_2032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_2030])).

tff(c_2033,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2371,plain,(
    ! [A_341,B_342,C_343] :
      ( k2_relset_1(A_341,B_342,C_343) = k2_relat_1(C_343)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2382,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_2371])).

tff(c_2386,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_2382])).

tff(c_2067,plain,(
    ! [B_284,A_285] :
      ( v4_relat_1(B_284,A_285)
      | ~ r1_tarski(k1_relat_1(B_284),A_285)
      | ~ v1_relat_1(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2072,plain,(
    ! [B_284] :
      ( v4_relat_1(B_284,k1_relat_1(B_284))
      | ~ v1_relat_1(B_284) ) ),
    inference(resolution,[status(thm)],[c_8,c_2067])).

tff(c_2217,plain,(
    ! [B_313,A_314] :
      ( k7_relat_1(B_313,A_314) = B_313
      | ~ v4_relat_1(B_313,A_314)
      | ~ v1_relat_1(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2254,plain,(
    ! [B_318] :
      ( k7_relat_1(B_318,k1_relat_1(B_318)) = B_318
      | ~ v1_relat_1(B_318) ) ),
    inference(resolution,[status(thm)],[c_2072,c_2217])).

tff(c_2490,plain,(
    ! [B_353] :
      ( k9_relat_1(B_353,k1_relat_1(B_353)) = k2_relat_1(B_353)
      | ~ v1_relat_1(B_353)
      | ~ v1_relat_1(B_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_52])).

tff(c_2452,plain,(
    ! [B_348,A_349] :
      ( k9_relat_1(B_348,A_349) != k1_xboole_0
      | ~ r1_tarski(A_349,k1_relat_1(B_348))
      | k1_xboole_0 = A_349
      | ~ v1_relat_1(B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2472,plain,(
    ! [B_348] :
      ( k9_relat_1(B_348,k1_relat_1(B_348)) != k1_xboole_0
      | k1_relat_1(B_348) = k1_xboole_0
      | ~ v1_relat_1(B_348) ) ),
    inference(resolution,[status(thm)],[c_8,c_2452])).

tff(c_3676,plain,(
    ! [B_465] :
      ( k2_relat_1(B_465) != k1_xboole_0
      | k1_relat_1(B_465) = k1_xboole_0
      | ~ v1_relat_1(B_465)
      | ~ v1_relat_1(B_465)
      | ~ v1_relat_1(B_465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2490,c_2472])).

tff(c_3686,plain,
    ( k2_relat_1('#skF_8') != k1_xboole_0
    | k1_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_141,c_3676])).

tff(c_3695,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2386,c_3686])).

tff(c_3697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2517,c_3695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:04:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.95  
% 5.05/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.95  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 5.05/1.95  
% 5.05/1.95  %Foreground sorts:
% 5.05/1.95  
% 5.05/1.95  
% 5.05/1.95  %Background operators:
% 5.05/1.95  
% 5.05/1.95  
% 5.05/1.95  %Foreground operators:
% 5.05/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.05/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.05/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.05/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/1.95  tff('#skF_7', type, '#skF_7': $i).
% 5.05/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.05/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.05/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.05/1.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.05/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.05/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.05/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.05/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.95  tff('#skF_8', type, '#skF_8': $i).
% 5.05/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.05/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.05/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.05/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.05/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.05/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.05/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.05/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.95  
% 5.05/1.97  tff(f_144, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 5.05/1.97  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.05/1.97  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.05/1.97  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.05/1.97  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.05/1.97  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.05/1.97  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.05/1.97  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.05/1.97  tff(f_51, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.05/1.97  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.05/1.97  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.05/1.97  tff(f_49, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 5.05/1.97  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.05/1.97  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/1.97  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.05/1.97  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.05/1.97  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.05/1.97  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.05/1.97  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 5.05/1.97  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.05/1.97  tff(c_2502, plain, (![A_354, B_355, C_356]: (k1_relset_1(A_354, B_355, C_356)=k1_relat_1(C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.05/1.97  tff(c_2516, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_2502])).
% 5.05/1.97  tff(c_68, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.05/1.97  tff(c_2517, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_68])).
% 5.05/1.97  tff(c_50, plain, (![A_39, B_40]: (v1_relat_1(k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.05/1.97  tff(c_126, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.05/1.97  tff(c_136, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_126])).
% 5.05/1.97  tff(c_141, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_136])).
% 5.05/1.97  tff(c_712, plain, (![A_180, B_181, C_182]: (k1_relset_1(A_180, B_181, C_182)=k1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.05/1.97  tff(c_732, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_712])).
% 5.05/1.97  tff(c_733, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_732, c_68])).
% 5.05/1.97  tff(c_195, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.05/1.97  tff(c_209, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_195])).
% 5.05/1.97  tff(c_48, plain, (![B_38, A_37]: (r1_tarski(k2_relat_1(B_38), A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.05/1.97  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.05/1.97  tff(c_30, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/1.97  tff(c_28, plain, (![A_24]: (k3_tarski(k1_zfmisc_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.05/1.97  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.05/1.97  tff(c_34, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | v1_xboole_0(B_29) | ~m1_subset_1(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.97  tff(c_375, plain, (![C_125, A_126, D_127]: (r2_hidden(C_125, k3_tarski(A_126)) | ~r2_hidden(D_127, A_126) | ~r2_hidden(C_125, D_127))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.05/1.97  tff(c_1051, plain, (![C_224, B_225, A_226]: (r2_hidden(C_224, k3_tarski(B_225)) | ~r2_hidden(C_224, A_226) | v1_xboole_0(B_225) | ~m1_subset_1(A_226, B_225))), inference(resolution, [status(thm)], [c_34, c_375])).
% 5.05/1.97  tff(c_1114, plain, (![A_231, B_232]: (r2_hidden('#skF_1'(A_231), k3_tarski(B_232)) | v1_xboole_0(B_232) | ~m1_subset_1(A_231, B_232) | k1_xboole_0=A_231)), inference(resolution, [status(thm)], [c_2, c_1051])).
% 5.05/1.97  tff(c_1124, plain, (![A_231, A_24]: (r2_hidden('#skF_1'(A_231), A_24) | v1_xboole_0(k1_zfmisc_1(A_24)) | ~m1_subset_1(A_231, k1_zfmisc_1(A_24)) | k1_xboole_0=A_231)), inference(superposition, [status(thm), theory('equality')], [c_28, c_1114])).
% 5.05/1.97  tff(c_1129, plain, (![A_233, A_234]: (r2_hidden('#skF_1'(A_233), A_234) | ~m1_subset_1(A_233, k1_zfmisc_1(A_234)) | k1_xboole_0=A_233)), inference(negUnitSimplification, [status(thm)], [c_30, c_1124])).
% 5.05/1.97  tff(c_32, plain, (![A_26, B_27]: (m1_subset_1(A_26, B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.05/1.97  tff(c_1166, plain, (![A_237, A_238]: (m1_subset_1('#skF_1'(A_237), A_238) | ~m1_subset_1(A_237, k1_zfmisc_1(A_238)) | k1_xboole_0=A_237)), inference(resolution, [status(thm)], [c_1129, c_32])).
% 5.05/1.97  tff(c_490, plain, (![A_150, B_151, C_152]: (k2_relset_1(A_150, B_151, C_152)=k2_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.05/1.97  tff(c_504, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_490])).
% 5.05/1.97  tff(c_90, plain, (![A_76]: (r2_hidden('#skF_1'(A_76), A_76) | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.05/1.97  tff(c_66, plain, (![D_67]: (~r2_hidden(D_67, k2_relset_1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1(D_67, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.05/1.97  tff(c_98, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_66])).
% 5.05/1.97  tff(c_153, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_98])).
% 5.05/1.97  tff(c_507, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_153])).
% 5.05/1.97  tff(c_1200, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_1166, c_507])).
% 5.05/1.97  tff(c_1206, plain, (~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1200])).
% 5.05/1.97  tff(c_1210, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_38, c_1206])).
% 5.05/1.97  tff(c_1240, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_1210])).
% 5.05/1.97  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_209, c_1240])).
% 5.05/1.97  tff(c_1245, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1200])).
% 5.05/1.97  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.05/1.97  tff(c_255, plain, (![B_109, A_110]: (v4_relat_1(B_109, A_110) | ~r1_tarski(k1_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.05/1.97  tff(c_260, plain, (![B_109]: (v4_relat_1(B_109, k1_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_8, c_255])).
% 5.05/1.97  tff(c_296, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=B_116 | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.05/1.97  tff(c_332, plain, (![B_119]: (k7_relat_1(B_119, k1_relat_1(B_119))=B_119 | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_260, c_296])).
% 5.05/1.97  tff(c_52, plain, (![B_42, A_41]: (k2_relat_1(k7_relat_1(B_42, A_41))=k9_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.05/1.97  tff(c_338, plain, (![B_119]: (k9_relat_1(B_119, k1_relat_1(B_119))=k2_relat_1(B_119) | ~v1_relat_1(B_119) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_332, c_52])).
% 5.05/1.97  tff(c_572, plain, (![B_161, A_162]: (k9_relat_1(B_161, A_162)!=k1_xboole_0 | ~r1_tarski(A_162, k1_relat_1(B_161)) | k1_xboole_0=A_162 | ~v1_relat_1(B_161))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.05/1.97  tff(c_593, plain, (![B_163]: (k9_relat_1(B_163, k1_relat_1(B_163))!=k1_xboole_0 | k1_relat_1(B_163)=k1_xboole_0 | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_8, c_572])).
% 5.05/1.97  tff(c_2011, plain, (![B_279]: (k2_relat_1(B_279)!=k1_xboole_0 | k1_relat_1(B_279)=k1_xboole_0 | ~v1_relat_1(B_279) | ~v1_relat_1(B_279) | ~v1_relat_1(B_279))), inference(superposition, [status(thm), theory('equality')], [c_338, c_593])).
% 5.05/1.97  tff(c_2021, plain, (k2_relat_1('#skF_8')!=k1_xboole_0 | k1_relat_1('#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_141, c_2011])).
% 5.05/1.97  tff(c_2030, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1245, c_2021])).
% 5.05/1.97  tff(c_2032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_733, c_2030])).
% 5.05/1.97  tff(c_2033, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_98])).
% 5.05/1.97  tff(c_2371, plain, (![A_341, B_342, C_343]: (k2_relset_1(A_341, B_342, C_343)=k2_relat_1(C_343) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.05/1.97  tff(c_2382, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_70, c_2371])).
% 5.05/1.97  tff(c_2386, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_2382])).
% 5.05/1.97  tff(c_2067, plain, (![B_284, A_285]: (v4_relat_1(B_284, A_285) | ~r1_tarski(k1_relat_1(B_284), A_285) | ~v1_relat_1(B_284))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.05/1.97  tff(c_2072, plain, (![B_284]: (v4_relat_1(B_284, k1_relat_1(B_284)) | ~v1_relat_1(B_284))), inference(resolution, [status(thm)], [c_8, c_2067])).
% 5.05/1.97  tff(c_2217, plain, (![B_313, A_314]: (k7_relat_1(B_313, A_314)=B_313 | ~v4_relat_1(B_313, A_314) | ~v1_relat_1(B_313))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.05/1.97  tff(c_2254, plain, (![B_318]: (k7_relat_1(B_318, k1_relat_1(B_318))=B_318 | ~v1_relat_1(B_318))), inference(resolution, [status(thm)], [c_2072, c_2217])).
% 5.05/1.97  tff(c_2490, plain, (![B_353]: (k9_relat_1(B_353, k1_relat_1(B_353))=k2_relat_1(B_353) | ~v1_relat_1(B_353) | ~v1_relat_1(B_353))), inference(superposition, [status(thm), theory('equality')], [c_2254, c_52])).
% 5.05/1.97  tff(c_2452, plain, (![B_348, A_349]: (k9_relat_1(B_348, A_349)!=k1_xboole_0 | ~r1_tarski(A_349, k1_relat_1(B_348)) | k1_xboole_0=A_349 | ~v1_relat_1(B_348))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.05/1.97  tff(c_2472, plain, (![B_348]: (k9_relat_1(B_348, k1_relat_1(B_348))!=k1_xboole_0 | k1_relat_1(B_348)=k1_xboole_0 | ~v1_relat_1(B_348))), inference(resolution, [status(thm)], [c_8, c_2452])).
% 5.05/1.97  tff(c_3676, plain, (![B_465]: (k2_relat_1(B_465)!=k1_xboole_0 | k1_relat_1(B_465)=k1_xboole_0 | ~v1_relat_1(B_465) | ~v1_relat_1(B_465) | ~v1_relat_1(B_465))), inference(superposition, [status(thm), theory('equality')], [c_2490, c_2472])).
% 5.05/1.97  tff(c_3686, plain, (k2_relat_1('#skF_8')!=k1_xboole_0 | k1_relat_1('#skF_8')=k1_xboole_0 | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_141, c_3676])).
% 5.05/1.97  tff(c_3695, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2386, c_3686])).
% 5.05/1.97  tff(c_3697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2517, c_3695])).
% 5.05/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.97  
% 5.05/1.97  Inference rules
% 5.05/1.97  ----------------------
% 5.05/1.97  #Ref     : 0
% 5.05/1.97  #Sup     : 754
% 5.05/1.97  #Fact    : 0
% 5.05/1.97  #Define  : 0
% 5.05/1.97  #Split   : 17
% 5.05/1.97  #Chain   : 0
% 5.05/1.97  #Close   : 0
% 5.05/1.97  
% 5.05/1.97  Ordering : KBO
% 5.05/1.97  
% 5.05/1.97  Simplification rules
% 5.05/1.97  ----------------------
% 5.05/1.97  #Subsume      : 60
% 5.05/1.97  #Demod        : 220
% 5.05/1.97  #Tautology    : 103
% 5.05/1.97  #SimpNegUnit  : 6
% 5.05/1.97  #BackRed      : 16
% 5.05/1.97  
% 5.05/1.97  #Partial instantiations: 0
% 5.05/1.97  #Strategies tried      : 1
% 5.05/1.97  
% 5.05/1.97  Timing (in seconds)
% 5.05/1.97  ----------------------
% 5.05/1.97  Preprocessing        : 0.32
% 5.05/1.97  Parsing              : 0.16
% 5.05/1.97  CNF conversion       : 0.03
% 5.05/1.97  Main loop            : 0.85
% 5.05/1.97  Inferencing          : 0.32
% 5.05/1.97  Reduction            : 0.24
% 5.05/1.97  Demodulation         : 0.16
% 5.05/1.97  BG Simplification    : 0.04
% 5.05/1.97  Subsumption          : 0.17
% 5.05/1.97  Abstraction          : 0.05
% 5.05/1.97  MUC search           : 0.00
% 5.05/1.97  Cooper               : 0.00
% 5.05/1.97  Total                : 1.21
% 5.05/1.97  Index Insertion      : 0.00
% 5.05/1.97  Index Deletion       : 0.00
% 5.05/1.97  Index Matching       : 0.00
% 5.05/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
