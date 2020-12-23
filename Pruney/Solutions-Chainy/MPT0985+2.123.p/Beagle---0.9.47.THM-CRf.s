%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  167 (1785 expanded)
%              Number of leaves         :   32 ( 598 expanded)
%              Depth                    :   16
%              Number of atoms          :  337 (6275 expanded)
%              Number of equality atoms :   87 (2026 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3423,plain,(
    ! [C_320,A_321,B_322] :
      ( v1_relat_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3436,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3423])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3547,plain,(
    ! [A_342,B_343,C_344] :
      ( k2_relset_1(A_342,B_343,C_344) = k2_relat_1(C_344)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3557,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3547])).

tff(c_3561,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3557])).

tff(c_24,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_189,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_180])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_258,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_267,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_258])).

tff(c_1714,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1727,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1714])).

tff(c_1735,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_267,c_1727])).

tff(c_1736,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1735])).

tff(c_22,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [A_25] :
      ( v1_funct_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_76,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_81,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_76])).

tff(c_84,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_81])).

tff(c_122,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_129])).

tff(c_136,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_226,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_226])).

tff(c_236,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_233])).

tff(c_329,plain,(
    ! [B_77,A_78] :
      ( v1_funct_2(B_77,k1_relat_1(B_77),A_78)
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2169,plain,(
    ! [A_225,A_226] :
      ( v1_funct_2(k2_funct_1(A_225),k2_relat_1(A_225),A_226)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_225)),A_226)
      | ~ v1_funct_1(k2_funct_1(A_225))
      | ~ v1_relat_1(k2_funct_1(A_225))
      | ~ v2_funct_1(A_225)
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_329])).

tff(c_2172,plain,(
    ! [A_226] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_226)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_226)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2169])).

tff(c_2180,plain,(
    ! [A_226] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_226)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_226)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_136,c_2172])).

tff(c_2226,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2180])).

tff(c_2229,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2226])).

tff(c_2233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_2229])).

tff(c_2235,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2180])).

tff(c_1554,plain,(
    ! [B_171,A_172] :
      ( m1_subset_1(B_171,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_171),A_172)))
      | ~ r1_tarski(k2_relat_1(B_171),A_172)
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2183,plain,(
    ! [A_227,A_228] :
      ( m1_subset_1(k2_funct_1(A_227),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_227),A_228)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_227)),A_228)
      | ~ v1_funct_1(k2_funct_1(A_227))
      | ~ v1_relat_1(k2_funct_1(A_227))
      | ~ v2_funct_1(A_227)
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1554])).

tff(c_2208,plain,(
    ! [A_228] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_228)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_228)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2183])).

tff(c_2223,plain,(
    ! [A_228] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_228)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_228)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_136,c_2208])).

tff(c_2238,plain,(
    ! [A_229] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_229)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_2223])).

tff(c_135,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_162,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_2271,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2238,c_162])).

tff(c_2275,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2271])).

tff(c_2278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_6,c_1736,c_2275])).

tff(c_2280,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1735])).

tff(c_2279,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1735])).

tff(c_34,plain,(
    ! [C_19,A_17] :
      ( k1_xboole_0 = C_19
      | ~ v1_funct_2(C_19,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2424,plain,(
    ! [C_242,A_243] :
      ( C_242 = '#skF_2'
      | ~ v1_funct_2(C_242,A_243,'#skF_2')
      | A_243 = '#skF_2'
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,'#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2279,c_2279,c_2279,c_34])).

tff(c_2439,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_2424])).

tff(c_2448,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2439])).

tff(c_2449,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2448])).

tff(c_2472,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2449,c_58])).

tff(c_140,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_140])).

tff(c_2469,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2449,c_148])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1667,plain,(
    ! [B_181,C_182] :
      ( k1_relset_1(k1_xboole_0,B_181,C_182) = k1_xboole_0
      | ~ v1_funct_2(C_182,k1_xboole_0,B_181)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1678,plain,(
    ! [B_181,A_4] :
      ( k1_relset_1(k1_xboole_0,B_181,A_4) = k1_xboole_0
      | ~ v1_funct_2(A_4,k1_xboole_0,B_181)
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_181)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1667])).

tff(c_2282,plain,(
    ! [B_181,A_4] :
      ( k1_relset_1('#skF_2',B_181,A_4) = '#skF_2'
      | ~ v1_funct_2(A_4,'#skF_2',B_181)
      | ~ r1_tarski(A_4,k2_zfmisc_1('#skF_2',B_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2279,c_2279,c_2279,c_1678])).

tff(c_2577,plain,(
    ! [B_248,A_249] :
      ( k1_relset_1('#skF_1',B_248,A_249) = '#skF_1'
      | ~ v1_funct_2(A_249,'#skF_1',B_248)
      | ~ r1_tarski(A_249,k2_zfmisc_1('#skF_1',B_248)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2449,c_2449,c_2449,c_2449,c_2282])).

tff(c_2580,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2469,c_2577])).

tff(c_2591,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2472,c_2580])).

tff(c_2464,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2449,c_267])).

tff(c_2691,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2591,c_2464])).

tff(c_2692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2280,c_2691])).

tff(c_2693,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2448])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2298,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_8])).

tff(c_2705,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_2298])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2300,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2279,c_16])).

tff(c_2702,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_2693,c_2300])).

tff(c_2710,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_236])).

tff(c_3267,plain,(
    ! [A_312,A_313] :
      ( v1_funct_2(k2_funct_1(A_312),k2_relat_1(A_312),A_313)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_312)),A_313)
      | ~ v1_funct_1(k2_funct_1(A_312))
      | ~ v1_relat_1(k2_funct_1(A_312))
      | ~ v2_funct_1(A_312)
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_329])).

tff(c_3270,plain,(
    ! [A_313] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_313)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_313)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2710,c_3267])).

tff(c_3275,plain,(
    ! [A_313] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_313)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_313)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_136,c_3270])).

tff(c_3276,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3275])).

tff(c_3279,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3276])).

tff(c_3283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_3279])).

tff(c_3285,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3275])).

tff(c_3304,plain,(
    ! [A_316,A_317] :
      ( m1_subset_1(k2_funct_1(A_316),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_316),A_317)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_316)),A_317)
      | ~ v1_funct_1(k2_funct_1(A_316))
      | ~ v1_relat_1(k2_funct_1(A_316))
      | ~ v2_funct_1(A_316)
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1554])).

tff(c_3329,plain,(
    ! [A_317] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_317)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_317)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2710,c_3304])).

tff(c_3343,plain,(
    ! [A_318] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_318)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_3285,c_136,c_3329])).

tff(c_2713,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2693,c_162])).

tff(c_3389,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3343,c_2713])).

tff(c_3397,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3389])).

tff(c_3400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_60,c_54,c_2705,c_2702,c_3397])).

tff(c_3401,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_3402,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_3479,plain,(
    ! [A_330,B_331,C_332] :
      ( k1_relset_1(A_330,B_331,C_332) = k1_relat_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3490,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3402,c_3479])).

tff(c_3767,plain,(
    ! [B_376,C_377,A_378] :
      ( k1_xboole_0 = B_376
      | v1_funct_2(C_377,A_378,B_376)
      | k1_relset_1(A_378,B_376,C_377) != A_378
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_378,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3773,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3402,c_3767])).

tff(c_3783,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3490,c_3773])).

tff(c_3784,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3401,c_3783])).

tff(c_3788,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3784])).

tff(c_3791,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3788])).

tff(c_3794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3436,c_60,c_54,c_3561,c_3791])).

tff(c_3795,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3784])).

tff(c_3814,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3795,c_8])).

tff(c_3492,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3479])).

tff(c_42,plain,(
    ! [B_18,A_17,C_19] :
      ( k1_xboole_0 = B_18
      | k1_relset_1(A_17,B_18,C_19) = A_17
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3899,plain,(
    ! [B_380,A_381,C_382] :
      ( B_380 = '#skF_1'
      | k1_relset_1(A_381,B_380,C_382) = A_381
      | ~ v1_funct_2(C_382,A_381,B_380)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_381,B_380))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3795,c_42])).

tff(c_3912,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_3899])).

tff(c_3918,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3492,c_3912])).

tff(c_3940,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3918])).

tff(c_3434,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3402,c_3423])).

tff(c_3796,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3784])).

tff(c_46,plain,(
    ! [B_21,A_20] :
      ( v1_funct_2(B_21,k1_relat_1(B_21),A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3831,plain,(
    ! [A_20] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_20)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_20)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_46])).

tff(c_4048,plain,(
    ! [A_395] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_395)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3434,c_136,c_3831])).

tff(c_4055,plain,(
    ! [A_395] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_395)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_395)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4048])).

tff(c_4062,plain,(
    ! [A_395] : v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_395) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3436,c_60,c_54,c_3814,c_3940,c_4055])).

tff(c_4067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4062,c_3401])).

tff(c_4068,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3918])).

tff(c_4083,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_3401])).

tff(c_3821,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_3490])).

tff(c_4074,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_4068,c_3821])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3419,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3402,c_10])).

tff(c_4081,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_3419])).

tff(c_3687,plain,(
    ! [C_366,B_367] :
      ( v1_funct_2(C_366,k1_xboole_0,B_367)
      | k1_relset_1(k1_xboole_0,B_367,C_366) != k1_xboole_0
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3692,plain,(
    ! [A_4,B_367] :
      ( v1_funct_2(A_4,k1_xboole_0,B_367)
      | k1_relset_1(k1_xboole_0,B_367,A_4) != k1_xboole_0
      | ~ r1_tarski(A_4,k2_zfmisc_1(k1_xboole_0,B_367)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3687])).

tff(c_4281,plain,(
    ! [A_402,B_403] :
      ( v1_funct_2(A_402,'#skF_1',B_403)
      | k1_relset_1('#skF_1',B_403,A_402) != '#skF_1'
      | ~ r1_tarski(A_402,k2_zfmisc_1('#skF_1',B_403)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3795,c_3795,c_3795,c_3795,c_3692])).

tff(c_4284,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_4081,c_4281])).

tff(c_4298,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_4284])).

tff(c_4300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4083,c_4298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.01  
% 5.31/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.01  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.31/2.01  
% 5.31/2.01  %Foreground sorts:
% 5.31/2.01  
% 5.31/2.01  
% 5.31/2.01  %Background operators:
% 5.31/2.01  
% 5.31/2.01  
% 5.31/2.01  %Foreground operators:
% 5.31/2.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.31/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.31/2.01  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.31/2.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.31/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.31/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.31/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.31/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.31/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.31/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.31/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.31/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.31/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.31/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.31/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/2.01  
% 5.31/2.03  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.31/2.03  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.31/2.03  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.31/2.03  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.31/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.31/2.03  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.31/2.03  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.31/2.03  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.31/2.03  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.31/2.03  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.31/2.03  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.31/2.03  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.31/2.03  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_3423, plain, (![C_320, A_321, B_322]: (v1_relat_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.31/2.03  tff(c_3436, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3423])).
% 5.31/2.03  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_3547, plain, (![A_342, B_343, C_344]: (k2_relset_1(A_342, B_343, C_344)=k2_relat_1(C_344) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.31/2.03  tff(c_3557, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3547])).
% 5.31/2.03  tff(c_3561, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3557])).
% 5.31/2.03  tff(c_24, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.03  tff(c_180, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.31/2.03  tff(c_189, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_180])).
% 5.31/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.31/2.03  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_258, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.31/2.03  tff(c_267, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_258])).
% 5.31/2.03  tff(c_1714, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_1727, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1714])).
% 5.31/2.03  tff(c_1735, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_267, c_1727])).
% 5.31/2.03  tff(c_1736, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1735])).
% 5.31/2.03  tff(c_22, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.03  tff(c_20, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.31/2.03  tff(c_78, plain, (![A_25]: (v1_funct_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.31/2.03  tff(c_50, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.31/2.03  tff(c_76, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.31/2.03  tff(c_81, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_76])).
% 5.31/2.03  tff(c_84, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_81])).
% 5.31/2.03  tff(c_122, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.31/2.03  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_122])).
% 5.31/2.03  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_129])).
% 5.31/2.03  tff(c_136, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 5.31/2.03  tff(c_226, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.31/2.03  tff(c_233, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_226])).
% 5.31/2.03  tff(c_236, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_233])).
% 5.31/2.03  tff(c_329, plain, (![B_77, A_78]: (v1_funct_2(B_77, k1_relat_1(B_77), A_78) | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.31/2.03  tff(c_2169, plain, (![A_225, A_226]: (v1_funct_2(k2_funct_1(A_225), k2_relat_1(A_225), A_226) | ~r1_tarski(k2_relat_1(k2_funct_1(A_225)), A_226) | ~v1_funct_1(k2_funct_1(A_225)) | ~v1_relat_1(k2_funct_1(A_225)) | ~v2_funct_1(A_225) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_24, c_329])).
% 5.31/2.03  tff(c_2172, plain, (![A_226]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_226) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_226) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_2169])).
% 5.31/2.03  tff(c_2180, plain, (![A_226]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_226) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_226) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_136, c_2172])).
% 5.31/2.03  tff(c_2226, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2180])).
% 5.31/2.03  tff(c_2229, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2226])).
% 5.31/2.03  tff(c_2233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_2229])).
% 5.31/2.03  tff(c_2235, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2180])).
% 5.31/2.03  tff(c_1554, plain, (![B_171, A_172]: (m1_subset_1(B_171, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_171), A_172))) | ~r1_tarski(k2_relat_1(B_171), A_172) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.31/2.03  tff(c_2183, plain, (![A_227, A_228]: (m1_subset_1(k2_funct_1(A_227), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_227), A_228))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_227)), A_228) | ~v1_funct_1(k2_funct_1(A_227)) | ~v1_relat_1(k2_funct_1(A_227)) | ~v2_funct_1(A_227) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1554])).
% 5.31/2.03  tff(c_2208, plain, (![A_228]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_228))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_228) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_2183])).
% 5.31/2.03  tff(c_2223, plain, (![A_228]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_228))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_228) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_136, c_2208])).
% 5.31/2.03  tff(c_2238, plain, (![A_229]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_229))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_229))), inference(demodulation, [status(thm), theory('equality')], [c_2235, c_2223])).
% 5.31/2.03  tff(c_135, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 5.31/2.03  tff(c_162, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_135])).
% 5.31/2.03  tff(c_2271, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_2238, c_162])).
% 5.31/2.03  tff(c_2275, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2271])).
% 5.31/2.03  tff(c_2278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_6, c_1736, c_2275])).
% 5.31/2.03  tff(c_2280, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_1735])).
% 5.31/2.03  tff(c_2279, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1735])).
% 5.31/2.03  tff(c_34, plain, (![C_19, A_17]: (k1_xboole_0=C_19 | ~v1_funct_2(C_19, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_2424, plain, (![C_242, A_243]: (C_242='#skF_2' | ~v1_funct_2(C_242, A_243, '#skF_2') | A_243='#skF_2' | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2279, c_2279, c_2279, c_34])).
% 5.31/2.03  tff(c_2439, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_2424])).
% 5.31/2.03  tff(c_2448, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2439])).
% 5.31/2.03  tff(c_2449, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_2448])).
% 5.31/2.03  tff(c_2472, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2449, c_58])).
% 5.31/2.03  tff(c_140, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.03  tff(c_148, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_140])).
% 5.31/2.03  tff(c_2469, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2449, c_148])).
% 5.31/2.03  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.03  tff(c_1667, plain, (![B_181, C_182]: (k1_relset_1(k1_xboole_0, B_181, C_182)=k1_xboole_0 | ~v1_funct_2(C_182, k1_xboole_0, B_181) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_181))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_1678, plain, (![B_181, A_4]: (k1_relset_1(k1_xboole_0, B_181, A_4)=k1_xboole_0 | ~v1_funct_2(A_4, k1_xboole_0, B_181) | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_181)))), inference(resolution, [status(thm)], [c_12, c_1667])).
% 5.31/2.03  tff(c_2282, plain, (![B_181, A_4]: (k1_relset_1('#skF_2', B_181, A_4)='#skF_2' | ~v1_funct_2(A_4, '#skF_2', B_181) | ~r1_tarski(A_4, k2_zfmisc_1('#skF_2', B_181)))), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2279, c_2279, c_2279, c_1678])).
% 5.31/2.03  tff(c_2577, plain, (![B_248, A_249]: (k1_relset_1('#skF_1', B_248, A_249)='#skF_1' | ~v1_funct_2(A_249, '#skF_1', B_248) | ~r1_tarski(A_249, k2_zfmisc_1('#skF_1', B_248)))), inference(demodulation, [status(thm), theory('equality')], [c_2449, c_2449, c_2449, c_2449, c_2282])).
% 5.31/2.03  tff(c_2580, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2469, c_2577])).
% 5.31/2.03  tff(c_2591, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2472, c_2580])).
% 5.31/2.03  tff(c_2464, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2449, c_267])).
% 5.31/2.03  tff(c_2691, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2591, c_2464])).
% 5.31/2.03  tff(c_2692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2280, c_2691])).
% 5.31/2.03  tff(c_2693, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_2448])).
% 5.31/2.03  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.31/2.03  tff(c_2298, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_8])).
% 5.31/2.03  tff(c_2705, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_2298])).
% 5.31/2.03  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.31/2.03  tff(c_2300, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2279, c_16])).
% 5.31/2.03  tff(c_2702, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_2693, c_2300])).
% 5.31/2.03  tff(c_2710, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_236])).
% 5.31/2.03  tff(c_3267, plain, (![A_312, A_313]: (v1_funct_2(k2_funct_1(A_312), k2_relat_1(A_312), A_313) | ~r1_tarski(k2_relat_1(k2_funct_1(A_312)), A_313) | ~v1_funct_1(k2_funct_1(A_312)) | ~v1_relat_1(k2_funct_1(A_312)) | ~v2_funct_1(A_312) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_24, c_329])).
% 5.31/2.03  tff(c_3270, plain, (![A_313]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_313) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_313) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2710, c_3267])).
% 5.31/2.03  tff(c_3275, plain, (![A_313]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_313) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_313) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_136, c_3270])).
% 5.31/2.03  tff(c_3276, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3275])).
% 5.31/2.03  tff(c_3279, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3276])).
% 5.31/2.03  tff(c_3283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_3279])).
% 5.31/2.03  tff(c_3285, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3275])).
% 5.31/2.03  tff(c_3304, plain, (![A_316, A_317]: (m1_subset_1(k2_funct_1(A_316), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_316), A_317))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_316)), A_317) | ~v1_funct_1(k2_funct_1(A_316)) | ~v1_relat_1(k2_funct_1(A_316)) | ~v2_funct_1(A_316) | ~v1_funct_1(A_316) | ~v1_relat_1(A_316))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1554])).
% 5.31/2.03  tff(c_3329, plain, (![A_317]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_317))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_317) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2710, c_3304])).
% 5.31/2.03  tff(c_3343, plain, (![A_318]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_318))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_318))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_3285, c_136, c_3329])).
% 5.31/2.03  tff(c_2713, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2693, c_162])).
% 5.31/2.03  tff(c_3389, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_3343, c_2713])).
% 5.31/2.03  tff(c_3397, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_3389])).
% 5.31/2.03  tff(c_3400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_60, c_54, c_2705, c_2702, c_3397])).
% 5.31/2.03  tff(c_3401, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_135])).
% 5.31/2.03  tff(c_3402, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_135])).
% 5.31/2.03  tff(c_3479, plain, (![A_330, B_331, C_332]: (k1_relset_1(A_330, B_331, C_332)=k1_relat_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.31/2.03  tff(c_3490, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3402, c_3479])).
% 5.31/2.03  tff(c_3767, plain, (![B_376, C_377, A_378]: (k1_xboole_0=B_376 | v1_funct_2(C_377, A_378, B_376) | k1_relset_1(A_378, B_376, C_377)!=A_378 | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_378, B_376))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_3773, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3402, c_3767])).
% 5.31/2.03  tff(c_3783, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3490, c_3773])).
% 5.31/2.03  tff(c_3784, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3401, c_3783])).
% 5.31/2.03  tff(c_3788, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3784])).
% 5.31/2.03  tff(c_3791, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_3788])).
% 5.31/2.03  tff(c_3794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3436, c_60, c_54, c_3561, c_3791])).
% 5.31/2.03  tff(c_3795, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3784])).
% 5.31/2.03  tff(c_3814, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3795, c_8])).
% 5.31/2.03  tff(c_3492, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3479])).
% 5.31/2.03  tff(c_42, plain, (![B_18, A_17, C_19]: (k1_xboole_0=B_18 | k1_relset_1(A_17, B_18, C_19)=A_17 | ~v1_funct_2(C_19, A_17, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_3899, plain, (![B_380, A_381, C_382]: (B_380='#skF_1' | k1_relset_1(A_381, B_380, C_382)=A_381 | ~v1_funct_2(C_382, A_381, B_380) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_381, B_380))))), inference(demodulation, [status(thm), theory('equality')], [c_3795, c_42])).
% 5.31/2.03  tff(c_3912, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_3899])).
% 5.31/2.03  tff(c_3918, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3492, c_3912])).
% 5.31/2.03  tff(c_3940, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_3918])).
% 5.31/2.03  tff(c_3434, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3402, c_3423])).
% 5.31/2.03  tff(c_3796, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_3784])).
% 5.31/2.03  tff(c_46, plain, (![B_21, A_20]: (v1_funct_2(B_21, k1_relat_1(B_21), A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.31/2.03  tff(c_3831, plain, (![A_20]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_20) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_20) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3796, c_46])).
% 5.31/2.03  tff(c_4048, plain, (![A_395]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_395) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_395))), inference(demodulation, [status(thm), theory('equality')], [c_3434, c_136, c_3831])).
% 5.31/2.03  tff(c_4055, plain, (![A_395]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_395) | ~r1_tarski(k1_relat_1('#skF_3'), A_395) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4048])).
% 5.31/2.03  tff(c_4062, plain, (![A_395]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_395))), inference(demodulation, [status(thm), theory('equality')], [c_3436, c_60, c_54, c_3814, c_3940, c_4055])).
% 5.31/2.03  tff(c_4067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4062, c_3401])).
% 5.31/2.03  tff(c_4068, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3918])).
% 5.31/2.03  tff(c_4083, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_3401])).
% 5.31/2.03  tff(c_3821, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_3490])).
% 5.31/2.03  tff(c_4074, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_4068, c_3821])).
% 5.31/2.03  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.03  tff(c_3419, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3402, c_10])).
% 5.31/2.03  tff(c_4081, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_3419])).
% 5.31/2.03  tff(c_3687, plain, (![C_366, B_367]: (v1_funct_2(C_366, k1_xboole_0, B_367) | k1_relset_1(k1_xboole_0, B_367, C_366)!=k1_xboole_0 | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_367))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.31/2.03  tff(c_3692, plain, (![A_4, B_367]: (v1_funct_2(A_4, k1_xboole_0, B_367) | k1_relset_1(k1_xboole_0, B_367, A_4)!=k1_xboole_0 | ~r1_tarski(A_4, k2_zfmisc_1(k1_xboole_0, B_367)))), inference(resolution, [status(thm)], [c_12, c_3687])).
% 5.31/2.03  tff(c_4281, plain, (![A_402, B_403]: (v1_funct_2(A_402, '#skF_1', B_403) | k1_relset_1('#skF_1', B_403, A_402)!='#skF_1' | ~r1_tarski(A_402, k2_zfmisc_1('#skF_1', B_403)))), inference(demodulation, [status(thm), theory('equality')], [c_3795, c_3795, c_3795, c_3795, c_3692])).
% 5.31/2.03  tff(c_4284, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_4081, c_4281])).
% 5.31/2.03  tff(c_4298, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_4284])).
% 5.31/2.03  tff(c_4300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4083, c_4298])).
% 5.31/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.03  
% 5.31/2.03  Inference rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Ref     : 0
% 5.31/2.03  #Sup     : 843
% 5.31/2.03  #Fact    : 0
% 5.31/2.03  #Define  : 0
% 5.31/2.03  #Split   : 21
% 5.31/2.03  #Chain   : 0
% 5.31/2.03  #Close   : 0
% 5.31/2.03  
% 5.31/2.03  Ordering : KBO
% 5.31/2.03  
% 5.31/2.03  Simplification rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Subsume      : 141
% 5.31/2.03  #Demod        : 1250
% 5.31/2.03  #Tautology    : 441
% 5.31/2.03  #SimpNegUnit  : 8
% 5.31/2.03  #BackRed      : 174
% 5.31/2.03  
% 5.31/2.03  #Partial instantiations: 0
% 5.31/2.03  #Strategies tried      : 1
% 5.31/2.03  
% 5.31/2.03  Timing (in seconds)
% 5.31/2.03  ----------------------
% 5.31/2.04  Preprocessing        : 0.32
% 5.31/2.04  Parsing              : 0.18
% 5.31/2.04  CNF conversion       : 0.02
% 5.31/2.04  Main loop            : 0.89
% 5.31/2.04  Inferencing          : 0.30
% 5.31/2.04  Reduction            : 0.31
% 5.31/2.04  Demodulation         : 0.22
% 5.31/2.04  BG Simplification    : 0.03
% 5.31/2.04  Subsumption          : 0.16
% 5.31/2.04  Abstraction          : 0.04
% 5.31/2.04  MUC search           : 0.00
% 5.31/2.04  Cooper               : 0.00
% 5.31/2.04  Total                : 1.26
% 5.31/2.04  Index Insertion      : 0.00
% 5.31/2.04  Index Deletion       : 0.00
% 5.31/2.04  Index Matching       : 0.00
% 5.31/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
