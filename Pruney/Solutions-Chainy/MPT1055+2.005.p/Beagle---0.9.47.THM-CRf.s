%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 134 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :  135 ( 362 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_769,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_776,plain,(
    ! [D_197] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_197) = k10_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_42,c_769])).

tff(c_99,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_238,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k8_relset_1(A_103,B_104,C_105,D_106) = k10_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_245,plain,(
    ! [D_106] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_106) = k10_relat_1('#skF_3',D_106) ),
    inference(resolution,[status(thm)],[c_42,c_238])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_109,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58])).

tff(c_248,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_109])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,k10_relat_1(B_12,A_11)),A_11)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_165,plain,(
    ! [C_84,A_85,B_86] :
      ( r1_tarski(k9_relat_1(C_84,A_85),k9_relat_1(C_84,B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_409,plain,(
    ! [C_136,A_137,B_138] :
      ( k2_xboole_0(k9_relat_1(C_136,A_137),k9_relat_1(C_136,B_138)) = k9_relat_1(C_136,B_138)
      | ~ r1_tarski(A_137,B_138)
      | ~ v1_relat_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_165,c_6])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_443,plain,(
    ! [C_142,A_143,C_144,B_145] :
      ( r1_tarski(k9_relat_1(C_142,A_143),C_144)
      | ~ r1_tarski(k9_relat_1(C_142,B_145),C_144)
      | ~ r1_tarski(A_143,B_145)
      | ~ v1_relat_1(C_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_4])).

tff(c_453,plain,(
    ! [B_146,A_147,A_148] :
      ( r1_tarski(k9_relat_1(B_146,A_147),A_148)
      | ~ r1_tarski(A_147,k10_relat_1(B_146,A_148))
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_14,c_443])).

tff(c_258,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k7_relset_1(A_108,B_109,C_110,D_111) = k9_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_265,plain,(
    ! [D_111] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_111) = k9_relat_1('#skF_3',D_111) ),
    inference(resolution,[status(thm)],[c_42,c_258])).

tff(c_270,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_60])).

tff(c_472,plain,
    ( ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_453,c_270])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46,c_248,c_472])).

tff(c_497,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_777,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_497])).

tff(c_592,plain,(
    ! [C_161,A_162,B_163] :
      ( v1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_601,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_592])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_499,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(A_149,B_150)
      | ~ m1_subset_1(A_149,k1_zfmisc_1(B_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_515,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_499])).

tff(c_44,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_716,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_725,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_716])).

tff(c_1329,plain,(
    ! [B_255,A_256,C_257] :
      ( k1_xboole_0 = B_255
      | k1_relset_1(A_256,B_255,C_257) = A_256
      | ~ v1_funct_2(C_257,A_256,B_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_256,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1336,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1329])).

tff(c_1340,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_725,c_1336])).

tff(c_1341,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1340])).

tff(c_831,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k7_relset_1(A_209,B_210,C_211,D_212) = k9_relat_1(C_211,D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_838,plain,(
    ! [D_212] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_212) = k9_relat_1('#skF_3',D_212) ),
    inference(resolution,[status(thm)],[c_42,c_831])).

tff(c_498,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_844,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_498])).

tff(c_1511,plain,(
    ! [A_271,C_272,B_273] :
      ( r1_tarski(A_271,k10_relat_1(C_272,B_273))
      | ~ r1_tarski(k9_relat_1(C_272,A_271),B_273)
      | ~ r1_tarski(A_271,k1_relat_1(C_272))
      | ~ v1_funct_1(C_272)
      | ~ v1_relat_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1529,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_844,c_1511])).

tff(c_1549,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_46,c_515,c_1341,c_1529])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_777,c_1549])).

tff(c_1552,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1340])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1564,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_2])).

tff(c_1566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.68  
% 3.83/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.68  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.83/1.68  
% 3.83/1.68  %Foreground sorts:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Background operators:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Foreground operators:
% 3.83/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.83/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.83/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.83/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.83/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.83/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.83/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.83/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.83/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.68  
% 3.83/1.70  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 3.83/1.70  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.83/1.70  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.83/1.70  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.83/1.70  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.83/1.70  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.83/1.70  tff(f_30, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.83/1.70  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.83/1.70  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.83/1.70  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.83/1.70  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.83/1.70  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.83/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.83/1.70  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_769, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.83/1.70  tff(c_776, plain, (![D_197]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_197)=k10_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_42, c_769])).
% 3.83/1.70  tff(c_99, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.83/1.70  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_99])).
% 3.83/1.70  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_238, plain, (![A_103, B_104, C_105, D_106]: (k8_relset_1(A_103, B_104, C_105, D_106)=k10_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.83/1.70  tff(c_245, plain, (![D_106]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_106)=k10_relat_1('#skF_3', D_106))), inference(resolution, [status(thm)], [c_42, c_238])).
% 3.83/1.70  tff(c_52, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_60, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 3.83/1.70  tff(c_58, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_109, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_58])).
% 3.83/1.70  tff(c_248, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_109])).
% 3.83/1.70  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, k10_relat_1(B_12, A_11)), A_11) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.83/1.70  tff(c_165, plain, (![C_84, A_85, B_86]: (r1_tarski(k9_relat_1(C_84, A_85), k9_relat_1(C_84, B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.70  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.83/1.70  tff(c_409, plain, (![C_136, A_137, B_138]: (k2_xboole_0(k9_relat_1(C_136, A_137), k9_relat_1(C_136, B_138))=k9_relat_1(C_136, B_138) | ~r1_tarski(A_137, B_138) | ~v1_relat_1(C_136))), inference(resolution, [status(thm)], [c_165, c_6])).
% 3.83/1.70  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.83/1.70  tff(c_443, plain, (![C_142, A_143, C_144, B_145]: (r1_tarski(k9_relat_1(C_142, A_143), C_144) | ~r1_tarski(k9_relat_1(C_142, B_145), C_144) | ~r1_tarski(A_143, B_145) | ~v1_relat_1(C_142))), inference(superposition, [status(thm), theory('equality')], [c_409, c_4])).
% 3.83/1.70  tff(c_453, plain, (![B_146, A_147, A_148]: (r1_tarski(k9_relat_1(B_146, A_147), A_148) | ~r1_tarski(A_147, k10_relat_1(B_146, A_148)) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_14, c_443])).
% 3.83/1.70  tff(c_258, plain, (![A_108, B_109, C_110, D_111]: (k7_relset_1(A_108, B_109, C_110, D_111)=k9_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/1.70  tff(c_265, plain, (![D_111]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_111)=k9_relat_1('#skF_3', D_111))), inference(resolution, [status(thm)], [c_42, c_258])).
% 3.83/1.70  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_60])).
% 3.83/1.70  tff(c_472, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_453, c_270])).
% 3.83/1.70  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_46, c_248, c_472])).
% 3.83/1.70  tff(c_497, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 3.83/1.70  tff(c_777, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_776, c_497])).
% 3.83/1.70  tff(c_592, plain, (![C_161, A_162, B_163]: (v1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.83/1.70  tff(c_601, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_592])).
% 3.83/1.70  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_499, plain, (![A_149, B_150]: (r1_tarski(A_149, B_150) | ~m1_subset_1(A_149, k1_zfmisc_1(B_150)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.70  tff(c_515, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_499])).
% 3.83/1.70  tff(c_44, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.83/1.70  tff(c_716, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.83/1.70  tff(c_725, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_716])).
% 3.83/1.70  tff(c_1329, plain, (![B_255, A_256, C_257]: (k1_xboole_0=B_255 | k1_relset_1(A_256, B_255, C_257)=A_256 | ~v1_funct_2(C_257, A_256, B_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.83/1.70  tff(c_1336, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1329])).
% 3.83/1.70  tff(c_1340, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_725, c_1336])).
% 3.83/1.70  tff(c_1341, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1340])).
% 3.83/1.70  tff(c_831, plain, (![A_209, B_210, C_211, D_212]: (k7_relset_1(A_209, B_210, C_211, D_212)=k9_relat_1(C_211, D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/1.70  tff(c_838, plain, (![D_212]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_212)=k9_relat_1('#skF_3', D_212))), inference(resolution, [status(thm)], [c_42, c_831])).
% 3.83/1.70  tff(c_498, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.83/1.70  tff(c_844, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_838, c_498])).
% 3.83/1.70  tff(c_1511, plain, (![A_271, C_272, B_273]: (r1_tarski(A_271, k10_relat_1(C_272, B_273)) | ~r1_tarski(k9_relat_1(C_272, A_271), B_273) | ~r1_tarski(A_271, k1_relat_1(C_272)) | ~v1_funct_1(C_272) | ~v1_relat_1(C_272))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.83/1.70  tff(c_1529, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_844, c_1511])).
% 3.83/1.70  tff(c_1549, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_46, c_515, c_1341, c_1529])).
% 3.83/1.70  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_777, c_1549])).
% 3.83/1.70  tff(c_1552, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1340])).
% 3.83/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.83/1.70  tff(c_1564, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1552, c_2])).
% 3.83/1.70  tff(c_1566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1564])).
% 3.83/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.70  
% 3.83/1.70  Inference rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Ref     : 0
% 3.83/1.70  #Sup     : 350
% 3.83/1.70  #Fact    : 0
% 3.83/1.70  #Define  : 0
% 3.83/1.70  #Split   : 13
% 3.83/1.70  #Chain   : 0
% 3.83/1.70  #Close   : 0
% 3.83/1.70  
% 3.83/1.70  Ordering : KBO
% 3.83/1.70  
% 3.83/1.70  Simplification rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Subsume      : 79
% 3.83/1.70  #Demod        : 108
% 3.83/1.70  #Tautology    : 100
% 3.83/1.70  #SimpNegUnit  : 4
% 3.83/1.70  #BackRed      : 24
% 3.83/1.70  
% 3.83/1.70  #Partial instantiations: 0
% 3.83/1.70  #Strategies tried      : 1
% 3.83/1.70  
% 3.83/1.70  Timing (in seconds)
% 3.83/1.70  ----------------------
% 3.83/1.70  Preprocessing        : 0.36
% 3.83/1.70  Parsing              : 0.19
% 3.83/1.70  CNF conversion       : 0.03
% 3.83/1.70  Main loop            : 0.51
% 3.83/1.70  Inferencing          : 0.18
% 3.83/1.70  Reduction            : 0.15
% 3.83/1.70  Demodulation         : 0.09
% 3.83/1.70  BG Simplification    : 0.03
% 3.83/1.70  Subsumption          : 0.10
% 3.83/1.70  Abstraction          : 0.03
% 3.83/1.70  MUC search           : 0.00
% 3.83/1.70  Cooper               : 0.00
% 3.83/1.70  Total                : 0.91
% 3.83/1.70  Index Insertion      : 0.00
% 3.83/1.70  Index Deletion       : 0.00
% 3.83/1.70  Index Matching       : 0.00
% 3.83/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
