%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:13 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 349 expanded)
%              Number of leaves         :   41 ( 134 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 742 expanded)
%              Number of equality atoms :   48 ( 135 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_908,plain,(
    ! [A_190,B_191,C_192] :
      ( k1_relset_1(A_190,B_191,C_192) = k1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_922,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_908])).

tff(c_44,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_923,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_44])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_108])).

tff(c_459,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_473,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_459])).

tff(c_479,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_44])).

tff(c_132,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_141,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_132])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_383,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_397,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_383])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_267,plain,(
    ! [A_103,C_104,B_105] :
      ( m1_subset_1(A_103,C_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(C_104))
      | ~ r2_hidden(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_307,plain,(
    ! [A_109,B_110,A_111] :
      ( m1_subset_1(A_109,B_110)
      | ~ r2_hidden(A_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_267])).

tff(c_314,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1('#skF_2'(A_112),B_113)
      | ~ r1_tarski(A_112,B_113)
      | k1_xboole_0 = A_112 ) ),
    inference(resolution,[status(thm)],[c_8,c_307])).

tff(c_96,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_60,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_101,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_155,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_339,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_155])).

tff(c_414,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_397,c_339])).

tff(c_415,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_418,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_415])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_141,c_418])).

tff(c_423,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_174,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_183,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_174])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_30])).

tff(c_189,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_186])).

tff(c_194,plain,(
    ! [B_88,A_89] :
      ( k2_relat_1(k7_relat_1(B_88,A_89)) = k9_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_206,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_194])).

tff(c_210,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_206])).

tff(c_428,plain,(
    k9_relat_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_210])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( r1_xboole_0(k1_relat_1(B_25),A_24)
      | k9_relat_1(B_25,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_275,plain,(
    ! [B_107,A_108] :
      ( k3_xboole_0(k1_relat_1(B_107),A_108) = k1_relat_1(k7_relat_1(B_107,A_108))
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_659,plain,(
    ! [B_145,A_146,C_147] :
      ( ~ r1_xboole_0(k1_relat_1(B_145),A_146)
      | ~ r2_hidden(C_147,k1_relat_1(k7_relat_1(B_145,A_146)))
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_6])).

tff(c_662,plain,(
    ! [C_147] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_147,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_659])).

tff(c_668,plain,(
    ! [C_147] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_147,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_662])).

tff(c_670,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_673,plain,
    ( k9_relat_1('#skF_5','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_670])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_428,c_673])).

tff(c_680,plain,(
    ! [C_148] : ~ r2_hidden(C_148,k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_684,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_680])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_684])).

tff(c_689,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_971,plain,(
    ! [A_195,B_196,C_197] :
      ( k2_relset_1(A_195,B_196,C_197) = k2_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_982,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_971])).

tff(c_986,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_982])).

tff(c_712,plain,(
    ! [C_157,A_158,B_159] :
      ( v4_relat_1(C_157,A_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_721,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_712])).

tff(c_747,plain,(
    ! [B_165,A_166] :
      ( k7_relat_1(B_165,A_166) = B_165
      | ~ v4_relat_1(B_165,A_166)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_750,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_721,c_747])).

tff(c_753,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_750])).

tff(c_758,plain,(
    ! [B_167,A_168] :
      ( k2_relat_1(k7_relat_1(B_167,A_168)) = k9_relat_1(B_167,A_168)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_773,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_758])).

tff(c_777,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_773])).

tff(c_987,plain,(
    k9_relat_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_777])).

tff(c_850,plain,(
    ! [B_184,A_185] :
      ( k3_xboole_0(k1_relat_1(B_184),A_185) = k1_relat_1(k7_relat_1(B_184,A_185))
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1096,plain,(
    ! [B_212,A_213,C_214] :
      ( ~ r1_xboole_0(k1_relat_1(B_212),A_213)
      | ~ r2_hidden(C_214,k1_relat_1(k7_relat_1(B_212,A_213)))
      | ~ v1_relat_1(B_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_6])).

tff(c_1099,plain,(
    ! [C_214] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_214,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_1096])).

tff(c_1105,plain,(
    ! [C_214] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_214,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1099])).

tff(c_1107,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1105])).

tff(c_1110,plain,
    ( k9_relat_1('#skF_5','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1107])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_987,c_1110])).

tff(c_1117,plain,(
    ! [C_215] : ~ r2_hidden(C_215,k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1105])).

tff(c_1121,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1117])).

tff(c_1125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_923,c_1121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:32:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.47  
% 3.20/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.48  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.48  
% 3.26/1.50  tff(f_129, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.26/1.50  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.50  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.26/1.50  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.50  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.50  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.50  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.26/1.50  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.50  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.50  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.26/1.50  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.26/1.50  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.26/1.50  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.26/1.50  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.26/1.50  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.26/1.50  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.50  tff(c_908, plain, (![A_190, B_191, C_192]: (k1_relset_1(A_190, B_191, C_192)=k1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.26/1.50  tff(c_922, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_908])).
% 3.26/1.50  tff(c_44, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.50  tff(c_923, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_922, c_44])).
% 3.26/1.50  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.50  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.26/1.50  tff(c_102, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.50  tff(c_108, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_102])).
% 3.26/1.50  tff(c_112, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_108])).
% 3.26/1.50  tff(c_459, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.26/1.50  tff(c_473, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_459])).
% 3.26/1.50  tff(c_479, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_473, c_44])).
% 3.26/1.50  tff(c_132, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.50  tff(c_141, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_132])).
% 3.26/1.50  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.50  tff(c_383, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.50  tff(c_397, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_383])).
% 3.26/1.50  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.50  tff(c_267, plain, (![A_103, C_104, B_105]: (m1_subset_1(A_103, C_104) | ~m1_subset_1(B_105, k1_zfmisc_1(C_104)) | ~r2_hidden(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.50  tff(c_307, plain, (![A_109, B_110, A_111]: (m1_subset_1(A_109, B_110) | ~r2_hidden(A_109, A_111) | ~r1_tarski(A_111, B_110))), inference(resolution, [status(thm)], [c_12, c_267])).
% 3.26/1.50  tff(c_314, plain, (![A_112, B_113]: (m1_subset_1('#skF_2'(A_112), B_113) | ~r1_tarski(A_112, B_113) | k1_xboole_0=A_112)), inference(resolution, [status(thm)], [c_8, c_307])).
% 3.26/1.50  tff(c_96, plain, (![D_60]: (~r2_hidden(D_60, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_60, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.50  tff(c_101, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_96])).
% 3.26/1.50  tff(c_155, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_101])).
% 3.26/1.50  tff(c_339, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_314, c_155])).
% 3.26/1.50  tff(c_414, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_397, c_397, c_339])).
% 3.26/1.50  tff(c_415, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_414])).
% 3.26/1.50  tff(c_418, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_415])).
% 3.26/1.50  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_141, c_418])).
% 3.26/1.50  tff(c_423, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_414])).
% 3.26/1.50  tff(c_174, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.50  tff(c_183, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_174])).
% 3.26/1.50  tff(c_30, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_186, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_183, c_30])).
% 3.26/1.50  tff(c_189, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_186])).
% 3.26/1.50  tff(c_194, plain, (![B_88, A_89]: (k2_relat_1(k7_relat_1(B_88, A_89))=k9_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.26/1.50  tff(c_206, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_189, c_194])).
% 3.26/1.50  tff(c_210, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_206])).
% 3.26/1.50  tff(c_428, plain, (k9_relat_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_423, c_210])).
% 3.26/1.50  tff(c_28, plain, (![B_25, A_24]: (r1_xboole_0(k1_relat_1(B_25), A_24) | k9_relat_1(B_25, A_24)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.26/1.50  tff(c_275, plain, (![B_107, A_108]: (k3_xboole_0(k1_relat_1(B_107), A_108)=k1_relat_1(k7_relat_1(B_107, A_108)) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.50  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.50  tff(c_659, plain, (![B_145, A_146, C_147]: (~r1_xboole_0(k1_relat_1(B_145), A_146) | ~r2_hidden(C_147, k1_relat_1(k7_relat_1(B_145, A_146))) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_275, c_6])).
% 3.26/1.50  tff(c_662, plain, (![C_147]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_147, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_659])).
% 3.26/1.50  tff(c_668, plain, (![C_147]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_147, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_662])).
% 3.26/1.50  tff(c_670, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_668])).
% 3.26/1.50  tff(c_673, plain, (k9_relat_1('#skF_5', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_670])).
% 3.26/1.50  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_428, c_673])).
% 3.26/1.50  tff(c_680, plain, (![C_148]: (~r2_hidden(C_148, k1_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_668])).
% 3.26/1.50  tff(c_684, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_680])).
% 3.26/1.50  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_479, c_684])).
% 3.26/1.50  tff(c_689, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_101])).
% 3.26/1.50  tff(c_971, plain, (![A_195, B_196, C_197]: (k2_relset_1(A_195, B_196, C_197)=k2_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.50  tff(c_982, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_971])).
% 3.26/1.50  tff(c_986, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_689, c_982])).
% 3.26/1.50  tff(c_712, plain, (![C_157, A_158, B_159]: (v4_relat_1(C_157, A_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.50  tff(c_721, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_712])).
% 3.26/1.50  tff(c_747, plain, (![B_165, A_166]: (k7_relat_1(B_165, A_166)=B_165 | ~v4_relat_1(B_165, A_166) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_750, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_721, c_747])).
% 3.26/1.50  tff(c_753, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_750])).
% 3.26/1.50  tff(c_758, plain, (![B_167, A_168]: (k2_relat_1(k7_relat_1(B_167, A_168))=k9_relat_1(B_167, A_168) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.26/1.50  tff(c_773, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_753, c_758])).
% 3.26/1.50  tff(c_777, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_773])).
% 3.26/1.50  tff(c_987, plain, (k9_relat_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_986, c_777])).
% 3.26/1.50  tff(c_850, plain, (![B_184, A_185]: (k3_xboole_0(k1_relat_1(B_184), A_185)=k1_relat_1(k7_relat_1(B_184, A_185)) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.50  tff(c_1096, plain, (![B_212, A_213, C_214]: (~r1_xboole_0(k1_relat_1(B_212), A_213) | ~r2_hidden(C_214, k1_relat_1(k7_relat_1(B_212, A_213))) | ~v1_relat_1(B_212))), inference(superposition, [status(thm), theory('equality')], [c_850, c_6])).
% 3.26/1.50  tff(c_1099, plain, (![C_214]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_214, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_1096])).
% 3.26/1.50  tff(c_1105, plain, (![C_214]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_214, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1099])).
% 3.26/1.50  tff(c_1107, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1105])).
% 3.26/1.50  tff(c_1110, plain, (k9_relat_1('#skF_5', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1107])).
% 3.26/1.50  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_987, c_1110])).
% 3.26/1.50  tff(c_1117, plain, (![C_215]: (~r2_hidden(C_215, k1_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1105])).
% 3.26/1.50  tff(c_1121, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1117])).
% 3.26/1.50  tff(c_1125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_923, c_1121])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 246
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 6
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 37
% 3.26/1.50  #Demod        : 59
% 3.26/1.50  #Tautology    : 72
% 3.26/1.50  #SimpNegUnit  : 2
% 3.26/1.50  #BackRed      : 10
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.33
% 3.26/1.50  Parsing              : 0.18
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.40
% 3.26/1.50  Inferencing          : 0.16
% 3.26/1.50  Reduction            : 0.12
% 3.26/1.50  Demodulation         : 0.08
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.06
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.77
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
