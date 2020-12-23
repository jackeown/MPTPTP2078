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
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 140 expanded)
%              Number of leaves         :   38 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 374 expanded)
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

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_822,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k8_relset_1(A_210,B_211,C_212,D_213) = k10_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_829,plain,(
    ! [D_213] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_213) = k10_relat_1('#skF_3',D_213) ),
    inference(resolution,[status(thm)],[c_44,c_822])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_121])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_252,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k8_relset_1(A_101,B_102,C_103,D_104) = k10_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_259,plain,(
    ! [D_104] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_104) = k10_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_102,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60])).

tff(c_263,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_102])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k9_relat_1(B_17,k10_relat_1(B_17,A_16)),A_16)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,(
    ! [C_92,A_93,B_94] :
      ( r1_tarski(k9_relat_1(C_92,A_93),k9_relat_1(C_92,B_94))
      | ~ r1_tarski(A_93,B_94)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_471,plain,(
    ! [C_153,A_154,B_155] :
      ( k2_xboole_0(k9_relat_1(C_153,A_154),k9_relat_1(C_153,B_155)) = k9_relat_1(C_153,B_155)
      | ~ r1_tarski(A_154,B_155)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_224,c_6])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_493,plain,(
    ! [C_156,A_157,C_158,B_159] :
      ( r1_tarski(k9_relat_1(C_156,A_157),C_158)
      | ~ r1_tarski(k9_relat_1(C_156,B_159),C_158)
      | ~ r1_tarski(A_157,B_159)
      | ~ v1_relat_1(C_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_4])).

tff(c_503,plain,(
    ! [B_160,A_161,A_162] :
      ( r1_tarski(k9_relat_1(B_160,A_161),A_162)
      | ~ r1_tarski(A_161,k10_relat_1(B_160,A_162))
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_18,c_493])).

tff(c_335,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_relset_1(A_121,B_122,C_123,D_124) = k9_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_342,plain,(
    ! [D_124] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_124) = k9_relat_1('#skF_3',D_124) ),
    inference(resolution,[status(thm)],[c_44,c_335])).

tff(c_343,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_62])).

tff(c_523,plain,
    ( ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_503,c_343])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48,c_263,c_523])).

tff(c_546,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_834,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_546])).

tff(c_589,plain,(
    ! [B_169,A_170] :
      ( v1_relat_1(B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_170))
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_595,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_589])).

tff(c_605,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_595])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_549,plain,(
    ! [A_165,B_166] :
      ( r1_tarski(A_165,B_166)
      | ~ m1_subset_1(A_165,k1_zfmisc_1(B_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_565,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_549])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_678,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_687,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_678])).

tff(c_1813,plain,(
    ! [B_332,A_333,C_334] :
      ( k1_xboole_0 = B_332
      | k1_relset_1(A_333,B_332,C_334) = A_333
      | ~ v1_funct_2(C_334,A_333,B_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1820,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1813])).

tff(c_1824,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_687,c_1820])).

tff(c_1825,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1824])).

tff(c_1485,plain,(
    ! [A_292,B_293,C_294,D_295] :
      ( k7_relset_1(A_292,B_293,C_294,D_295) = k9_relat_1(C_294,D_295)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1492,plain,(
    ! [D_295] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_295) = k9_relat_1('#skF_3',D_295) ),
    inference(resolution,[status(thm)],[c_44,c_1485])).

tff(c_547,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1498,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_547])).

tff(c_2274,plain,(
    ! [A_365,C_366,B_367] :
      ( r1_tarski(A_365,k10_relat_1(C_366,B_367))
      | ~ r1_tarski(k9_relat_1(C_366,A_365),B_367)
      | ~ r1_tarski(A_365,k1_relat_1(C_366))
      | ~ v1_funct_1(C_366)
      | ~ v1_relat_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2289,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1498,c_2274])).

tff(c_2308,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_48,c_565,c_1825,c_2289])).

tff(c_2310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_2308])).

tff(c_2311,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2326,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2])).

tff(c_2328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.89  
% 4.72/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.89  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.72/1.89  
% 4.72/1.89  %Foreground sorts:
% 4.72/1.89  
% 4.72/1.89  
% 4.72/1.89  %Background operators:
% 4.72/1.89  
% 4.72/1.89  
% 4.72/1.89  %Foreground operators:
% 4.72/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.89  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.72/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.89  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.72/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.72/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.72/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.72/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.72/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.72/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.72/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.72/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.72/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.89  
% 4.72/1.91  tff(f_124, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 4.72/1.91  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.72/1.91  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.72/1.91  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.72/1.91  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 4.72/1.91  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 4.72/1.91  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.72/1.91  tff(f_30, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.72/1.91  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.72/1.91  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.91  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.72/1.91  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.72/1.91  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 4.72/1.91  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.72/1.91  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_822, plain, (![A_210, B_211, C_212, D_213]: (k8_relset_1(A_210, B_211, C_212, D_213)=k10_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.72/1.91  tff(c_829, plain, (![D_213]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_213)=k10_relat_1('#skF_3', D_213))), inference(resolution, [status(thm)], [c_44, c_822])).
% 4.72/1.91  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.72/1.91  tff(c_121, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.72/1.91  tff(c_127, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_121])).
% 4.72/1.91  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_127])).
% 4.72/1.91  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_252, plain, (![A_101, B_102, C_103, D_104]: (k8_relset_1(A_101, B_102, C_103, D_104)=k10_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.72/1.91  tff(c_259, plain, (![D_104]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_104)=k10_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_44, c_252])).
% 4.72/1.91  tff(c_54, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_62, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 4.72/1.91  tff(c_60, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_102, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_60])).
% 4.72/1.91  tff(c_263, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_102])).
% 4.72/1.91  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k9_relat_1(B_17, k10_relat_1(B_17, A_16)), A_16) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.72/1.91  tff(c_224, plain, (![C_92, A_93, B_94]: (r1_tarski(k9_relat_1(C_92, A_93), k9_relat_1(C_92, B_94)) | ~r1_tarski(A_93, B_94) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.72/1.91  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.72/1.91  tff(c_471, plain, (![C_153, A_154, B_155]: (k2_xboole_0(k9_relat_1(C_153, A_154), k9_relat_1(C_153, B_155))=k9_relat_1(C_153, B_155) | ~r1_tarski(A_154, B_155) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_224, c_6])).
% 4.72/1.91  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.72/1.91  tff(c_493, plain, (![C_156, A_157, C_158, B_159]: (r1_tarski(k9_relat_1(C_156, A_157), C_158) | ~r1_tarski(k9_relat_1(C_156, B_159), C_158) | ~r1_tarski(A_157, B_159) | ~v1_relat_1(C_156))), inference(superposition, [status(thm), theory('equality')], [c_471, c_4])).
% 4.72/1.91  tff(c_503, plain, (![B_160, A_161, A_162]: (r1_tarski(k9_relat_1(B_160, A_161), A_162) | ~r1_tarski(A_161, k10_relat_1(B_160, A_162)) | ~v1_funct_1(B_160) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_18, c_493])).
% 4.72/1.91  tff(c_335, plain, (![A_121, B_122, C_123, D_124]: (k7_relset_1(A_121, B_122, C_123, D_124)=k9_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.72/1.91  tff(c_342, plain, (![D_124]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_124)=k9_relat_1('#skF_3', D_124))), inference(resolution, [status(thm)], [c_44, c_335])).
% 4.72/1.91  tff(c_343, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_62])).
% 4.72/1.91  tff(c_523, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_503, c_343])).
% 4.72/1.91  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_48, c_263, c_523])).
% 4.72/1.91  tff(c_546, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_54])).
% 4.72/1.91  tff(c_834, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_829, c_546])).
% 4.72/1.91  tff(c_589, plain, (![B_169, A_170]: (v1_relat_1(B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(A_170)) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.72/1.91  tff(c_595, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_589])).
% 4.72/1.91  tff(c_605, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_595])).
% 4.72/1.91  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_549, plain, (![A_165, B_166]: (r1_tarski(A_165, B_166) | ~m1_subset_1(A_165, k1_zfmisc_1(B_166)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.72/1.91  tff(c_565, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_549])).
% 4.72/1.91  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.72/1.91  tff(c_678, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.72/1.91  tff(c_687, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_678])).
% 4.72/1.91  tff(c_1813, plain, (![B_332, A_333, C_334]: (k1_xboole_0=B_332 | k1_relset_1(A_333, B_332, C_334)=A_333 | ~v1_funct_2(C_334, A_333, B_332) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.72/1.91  tff(c_1820, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1813])).
% 4.72/1.91  tff(c_1824, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_687, c_1820])).
% 4.72/1.91  tff(c_1825, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1824])).
% 4.72/1.91  tff(c_1485, plain, (![A_292, B_293, C_294, D_295]: (k7_relset_1(A_292, B_293, C_294, D_295)=k9_relat_1(C_294, D_295) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.72/1.91  tff(c_1492, plain, (![D_295]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_295)=k9_relat_1('#skF_3', D_295))), inference(resolution, [status(thm)], [c_44, c_1485])).
% 4.72/1.91  tff(c_547, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 4.72/1.91  tff(c_1498, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_547])).
% 4.72/1.91  tff(c_2274, plain, (![A_365, C_366, B_367]: (r1_tarski(A_365, k10_relat_1(C_366, B_367)) | ~r1_tarski(k9_relat_1(C_366, A_365), B_367) | ~r1_tarski(A_365, k1_relat_1(C_366)) | ~v1_funct_1(C_366) | ~v1_relat_1(C_366))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.91  tff(c_2289, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1498, c_2274])).
% 4.72/1.91  tff(c_2308, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_605, c_48, c_565, c_1825, c_2289])).
% 4.72/1.91  tff(c_2310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_2308])).
% 4.72/1.91  tff(c_2311, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1824])).
% 4.72/1.91  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.72/1.91  tff(c_2326, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2])).
% 4.72/1.91  tff(c_2328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2326])).
% 4.72/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.91  
% 4.72/1.91  Inference rules
% 4.72/1.91  ----------------------
% 4.72/1.91  #Ref     : 0
% 4.72/1.91  #Sup     : 494
% 4.72/1.91  #Fact    : 0
% 4.72/1.91  #Define  : 0
% 4.72/1.91  #Split   : 23
% 4.72/1.91  #Chain   : 0
% 4.72/1.91  #Close   : 0
% 4.72/1.91  
% 4.72/1.91  Ordering : KBO
% 4.72/1.91  
% 4.72/1.91  Simplification rules
% 4.72/1.91  ----------------------
% 4.72/1.91  #Subsume      : 75
% 4.72/1.91  #Demod        : 325
% 4.72/1.91  #Tautology    : 137
% 4.72/1.91  #SimpNegUnit  : 6
% 4.72/1.91  #BackRed      : 81
% 4.72/1.91  
% 4.72/1.91  #Partial instantiations: 0
% 4.72/1.91  #Strategies tried      : 1
% 4.72/1.91  
% 4.72/1.91  Timing (in seconds)
% 4.72/1.91  ----------------------
% 4.72/1.91  Preprocessing        : 0.35
% 4.72/1.91  Parsing              : 0.18
% 4.72/1.91  CNF conversion       : 0.03
% 4.72/1.91  Main loop            : 0.78
% 4.72/1.91  Inferencing          : 0.28
% 4.72/1.91  Reduction            : 0.23
% 4.72/1.91  Demodulation         : 0.15
% 4.72/1.91  BG Simplification    : 0.04
% 4.72/1.91  Subsumption          : 0.15
% 4.72/1.91  Abstraction          : 0.04
% 4.72/1.91  MUC search           : 0.00
% 4.72/1.91  Cooper               : 0.00
% 4.72/1.91  Total                : 1.17
% 4.72/1.91  Index Insertion      : 0.00
% 4.72/1.91  Index Deletion       : 0.00
% 4.72/1.91  Index Matching       : 0.00
% 4.72/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
