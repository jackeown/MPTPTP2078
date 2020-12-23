%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 637 expanded)
%              Number of leaves         :   31 ( 214 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 (1430 expanded)
%              Number of equality atoms :   60 ( 447 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_4103,plain,(
    ! [A_406,B_407] :
      ( r1_tarski(A_406,B_407)
      | ~ m1_subset_1(A_406,k1_zfmisc_1(B_407)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4110,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_57,c_4103])).

tff(c_4362,plain,(
    ! [C_446,A_447,B_448] :
      ( m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ r1_tarski(k2_relat_1(C_446),B_448)
      | ~ r1_tarski(k1_relat_1(C_446),A_447)
      | ~ v1_relat_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2898,plain,(
    ! [C_313,B_314] :
      ( v1_funct_2(C_313,k1_xboole_0,B_314)
      | k1_relset_1(k1_xboole_0,B_314,C_313) != k1_xboole_0
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_3613,plain,(
    ! [A_374,B_375] :
      ( v1_funct_2(A_374,k1_xboole_0,B_375)
      | k1_relset_1(k1_xboole_0,B_375,A_374) != k1_xboole_0
      | ~ r1_tarski(A_374,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2898])).

tff(c_152,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_57,c_152])).

tff(c_391,plain,(
    ! [C_72,A_73,B_74] :
      ( m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ r1_tarski(k2_relat_1(C_72),B_74)
      | ~ r1_tarski(k1_relat_1(C_72),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1096,plain,(
    ! [C_150,A_151,B_152] :
      ( r1_tarski(C_150,k2_zfmisc_1(A_151,B_152))
      | ~ r1_tarski(k2_relat_1(C_150),B_152)
      | ~ r1_tarski(k1_relat_1(C_150),A_151)
      | ~ v1_relat_1(C_150) ) ),
    inference(resolution,[status(thm)],[c_391,c_18])).

tff(c_1113,plain,(
    ! [C_153,A_154] :
      ( r1_tarski(C_153,k2_zfmisc_1(A_154,k2_relat_1(C_153)))
      | ~ r1_tarski(k1_relat_1(C_153),A_154)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_163,c_1096])).

tff(c_314,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_333,plain,(
    ! [A_65,B_66,A_7] :
      ( k1_relset_1(A_65,B_66,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_20,c_314])).

tff(c_1299,plain,(
    ! [A_169,C_170] :
      ( k1_relset_1(A_169,k2_relat_1(C_170),C_170) = k1_relat_1(C_170)
      | ~ r1_tarski(k1_relat_1(C_170),A_169)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_1113,c_333])).

tff(c_1315,plain,(
    ! [C_170] :
      ( k1_relset_1(k1_relat_1(C_170),k2_relat_1(C_170),C_170) = k1_relat_1(C_170)
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_163,c_1299])).

tff(c_166,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | k1_relat_1(A_42) != k1_xboole_0
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_166])).

tff(c_172,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_173,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | k2_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_173])).

tff(c_179,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_176])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_605,plain,(
    ! [B_96,C_97,A_98] :
      ( k1_xboole_0 = B_96
      | v1_funct_2(C_97,A_98,B_96)
      | k1_relset_1(A_98,B_96,C_97) != A_98
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1837,plain,(
    ! [B_220,C_221,A_222] :
      ( k1_xboole_0 = B_220
      | v1_funct_2(C_221,A_222,B_220)
      | k1_relset_1(A_222,B_220,C_221) != A_222
      | ~ r1_tarski(k2_relat_1(C_221),B_220)
      | ~ r1_tarski(k1_relat_1(C_221),A_222)
      | ~ v1_relat_1(C_221) ) ),
    inference(resolution,[status(thm)],[c_34,c_605])).

tff(c_2378,plain,(
    ! [C_259,A_260] :
      ( k2_relat_1(C_259) = k1_xboole_0
      | v1_funct_2(C_259,A_260,k2_relat_1(C_259))
      | k1_relset_1(A_260,k2_relat_1(C_259),C_259) != A_260
      | ~ r1_tarski(k1_relat_1(C_259),A_260)
      | ~ v1_relat_1(C_259) ) ),
    inference(resolution,[status(thm)],[c_163,c_1837])).

tff(c_50,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_100,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2398,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2378,c_100])).

tff(c_2419,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163,c_2398])).

tff(c_2420,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_2419])).

tff(c_2427,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_2420])).

tff(c_2437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2427])).

tff(c_2439,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_2438,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_2440,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_100])).

tff(c_2457,plain,(
    ~ v1_funct_2('#skF_1',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2439,c_2440])).

tff(c_3625,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') != k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3613,c_2457])).

tff(c_3626,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3625])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_164,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_152])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2770,plain,(
    ! [C_300,A_301,B_302] :
      ( m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302)))
      | ~ r1_tarski(k2_relat_1(C_300),B_302)
      | ~ r1_tarski(k1_relat_1(C_300),A_301)
      | ~ v1_relat_1(C_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3846,plain,(
    ! [C_395,A_396] :
      ( m1_subset_1(C_395,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_395),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_395),A_396)
      | ~ v1_relat_1(C_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2770])).

tff(c_3850,plain,(
    ! [A_396] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_396)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2438,c_3846])).

tff(c_3858,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_164,c_2439,c_164,c_3850])).

tff(c_3878,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3858,c_18])).

tff(c_3891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3626,c_3878])).

tff(c_3893,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3625])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2476,plain,(
    ! [C_264,B_265,A_266] :
      ( v1_xboole_0(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(B_265,A_266)))
      | ~ v1_xboole_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2487,plain,(
    ! [C_264] :
      ( v1_xboole_0(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2476])).

tff(c_2519,plain,(
    ! [C_269] :
      ( v1_xboole_0(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2487])).

tff(c_2532,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2519])).

tff(c_3905,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3893,c_2532])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3917,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3905,c_4])).

tff(c_3028,plain,(
    ! [A_328,B_329] :
      ( v1_funct_2(A_328,k1_xboole_0,B_329)
      | k1_relset_1(k1_xboole_0,B_329,A_328) != k1_xboole_0
      | ~ r1_tarski(A_328,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2898])).

tff(c_3037,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_1') != k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3028,c_2457])).

tff(c_3057,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3037])).

tff(c_3249,plain,(
    ! [C_348,B_349] :
      ( m1_subset_1(C_348,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_348),B_349)
      | ~ r1_tarski(k1_relat_1(C_348),k1_xboole_0)
      | ~ v1_relat_1(C_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2770])).

tff(c_3255,plain,(
    ! [B_349] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,B_349)
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_xboole_0)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2438,c_3249])).

tff(c_3268,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_164,c_2439,c_164,c_3255])).

tff(c_3289,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3268,c_18])).

tff(c_3302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3057,c_3289])).

tff(c_3304,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3037])).

tff(c_3316,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3304,c_2532])).

tff(c_3328,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3316,c_4])).

tff(c_3355,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_2439])).

tff(c_2562,plain,(
    ! [A_278,B_279,C_280] :
      ( k1_relset_1(A_278,B_279,C_280) = k1_relat_1(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2583,plain,(
    ! [A_278,B_279] : k1_relset_1(A_278,B_279,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_2562])).

tff(c_2904,plain,(
    ! [B_314] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_314)
      | k1_relset_1(k1_xboole_0,B_314,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_57,c_2898])).

tff(c_2910,plain,(
    ! [B_314] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_314)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2583,c_2904])).

tff(c_2913,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2910])).

tff(c_3337,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_3328,c_2913])).

tff(c_3419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_3337])).

tff(c_3420,plain,(
    ! [B_314] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_314) ),
    inference(splitRight,[status(thm)],[c_2910])).

tff(c_3927,plain,(
    ! [B_314] : v1_funct_2('#skF_1','#skF_1',B_314) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3917,c_3917,c_3420])).

tff(c_3943,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3917,c_3917,c_2457])).

tff(c_4050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3927,c_3943])).

tff(c_4051,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4376,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4362,c_4051])).

tff(c_4393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4110,c_4110,c_4376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.08  
% 5.41/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.08  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.50/2.08  
% 5.50/2.08  %Foreground sorts:
% 5.50/2.08  
% 5.50/2.08  
% 5.50/2.08  %Background operators:
% 5.50/2.08  
% 5.50/2.08  
% 5.50/2.08  %Foreground operators:
% 5.50/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.50/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.50/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.50/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.50/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.50/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.50/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.50/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.50/2.08  
% 5.50/2.10  tff(f_110, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.50/2.10  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.50/2.10  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.50/2.10  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.50/2.10  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.50/2.10  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.50/2.10  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.50/2.10  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.50/2.10  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 5.50/2.10  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.50/2.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.50/2.10  tff(f_69, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.50/2.10  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.50/2.10  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.50/2.10  tff(c_12, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.50/2.10  tff(c_14, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.50/2.10  tff(c_57, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 5.50/2.10  tff(c_4103, plain, (![A_406, B_407]: (r1_tarski(A_406, B_407) | ~m1_subset_1(A_406, k1_zfmisc_1(B_407)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_4110, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_57, c_4103])).
% 5.50/2.10  tff(c_4362, plain, (![C_446, A_447, B_448]: (m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~r1_tarski(k2_relat_1(C_446), B_448) | ~r1_tarski(k1_relat_1(C_446), A_447) | ~v1_relat_1(C_446))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.50/2.10  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.50/2.10  tff(c_40, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.50/2.10  tff(c_2898, plain, (![C_313, B_314]: (v1_funct_2(C_313, k1_xboole_0, B_314) | k1_relset_1(k1_xboole_0, B_314, C_313)!=k1_xboole_0 | ~m1_subset_1(C_313, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 5.50/2.10  tff(c_3613, plain, (![A_374, B_375]: (v1_funct_2(A_374, k1_xboole_0, B_375) | k1_relset_1(k1_xboole_0, B_375, A_374)!=k1_xboole_0 | ~r1_tarski(A_374, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2898])).
% 5.50/2.10  tff(c_152, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_163, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_57, c_152])).
% 5.50/2.10  tff(c_391, plain, (![C_72, A_73, B_74]: (m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~r1_tarski(k2_relat_1(C_72), B_74) | ~r1_tarski(k1_relat_1(C_72), A_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.50/2.10  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_1096, plain, (![C_150, A_151, B_152]: (r1_tarski(C_150, k2_zfmisc_1(A_151, B_152)) | ~r1_tarski(k2_relat_1(C_150), B_152) | ~r1_tarski(k1_relat_1(C_150), A_151) | ~v1_relat_1(C_150))), inference(resolution, [status(thm)], [c_391, c_18])).
% 5.50/2.10  tff(c_1113, plain, (![C_153, A_154]: (r1_tarski(C_153, k2_zfmisc_1(A_154, k2_relat_1(C_153))) | ~r1_tarski(k1_relat_1(C_153), A_154) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_163, c_1096])).
% 5.50/2.10  tff(c_314, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_333, plain, (![A_65, B_66, A_7]: (k1_relset_1(A_65, B_66, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_20, c_314])).
% 5.50/2.10  tff(c_1299, plain, (![A_169, C_170]: (k1_relset_1(A_169, k2_relat_1(C_170), C_170)=k1_relat_1(C_170) | ~r1_tarski(k1_relat_1(C_170), A_169) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_1113, c_333])).
% 5.50/2.10  tff(c_1315, plain, (![C_170]: (k1_relset_1(k1_relat_1(C_170), k2_relat_1(C_170), C_170)=k1_relat_1(C_170) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_163, c_1299])).
% 5.50/2.10  tff(c_166, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | k1_relat_1(A_42)!=k1_xboole_0 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.10  tff(c_170, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_166])).
% 5.50/2.10  tff(c_172, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_170])).
% 5.50/2.10  tff(c_173, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | k2_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.10  tff(c_176, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_173])).
% 5.50/2.10  tff(c_179, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_172, c_176])).
% 5.50/2.10  tff(c_34, plain, (![C_23, A_21, B_22]: (m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~r1_tarski(k2_relat_1(C_23), B_22) | ~r1_tarski(k1_relat_1(C_23), A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.50/2.10  tff(c_605, plain, (![B_96, C_97, A_98]: (k1_xboole_0=B_96 | v1_funct_2(C_97, A_98, B_96) | k1_relset_1(A_98, B_96, C_97)!=A_98 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.50/2.10  tff(c_1837, plain, (![B_220, C_221, A_222]: (k1_xboole_0=B_220 | v1_funct_2(C_221, A_222, B_220) | k1_relset_1(A_222, B_220, C_221)!=A_222 | ~r1_tarski(k2_relat_1(C_221), B_220) | ~r1_tarski(k1_relat_1(C_221), A_222) | ~v1_relat_1(C_221))), inference(resolution, [status(thm)], [c_34, c_605])).
% 5.50/2.10  tff(c_2378, plain, (![C_259, A_260]: (k2_relat_1(C_259)=k1_xboole_0 | v1_funct_2(C_259, A_260, k2_relat_1(C_259)) | k1_relset_1(A_260, k2_relat_1(C_259), C_259)!=A_260 | ~r1_tarski(k1_relat_1(C_259), A_260) | ~v1_relat_1(C_259))), inference(resolution, [status(thm)], [c_163, c_1837])).
% 5.50/2.10  tff(c_50, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.50/2.10  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.50/2.10  tff(c_54, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 5.50/2.10  tff(c_100, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.50/2.10  tff(c_2398, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2378, c_100])).
% 5.50/2.10  tff(c_2419, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_163, c_2398])).
% 5.50/2.10  tff(c_2420, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_179, c_2419])).
% 5.50/2.10  tff(c_2427, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1315, c_2420])).
% 5.50/2.10  tff(c_2437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_2427])).
% 5.50/2.10  tff(c_2439, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_170])).
% 5.50/2.10  tff(c_2438, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_170])).
% 5.50/2.10  tff(c_2440, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2438, c_100])).
% 5.50/2.10  tff(c_2457, plain, (~v1_funct_2('#skF_1', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2439, c_2440])).
% 5.50/2.10  tff(c_3625, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')!=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_3613, c_2457])).
% 5.50/2.10  tff(c_3626, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3625])).
% 5.50/2.10  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.50/2.10  tff(c_164, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_152])).
% 5.50/2.10  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.50/2.10  tff(c_2770, plain, (![C_300, A_301, B_302]: (m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))) | ~r1_tarski(k2_relat_1(C_300), B_302) | ~r1_tarski(k1_relat_1(C_300), A_301) | ~v1_relat_1(C_300))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.50/2.10  tff(c_3846, plain, (![C_395, A_396]: (m1_subset_1(C_395, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_395), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_395), A_396) | ~v1_relat_1(C_395))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2770])).
% 5.50/2.10  tff(c_3850, plain, (![A_396]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_1'), A_396) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2438, c_3846])).
% 5.50/2.10  tff(c_3858, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_164, c_2439, c_164, c_3850])).
% 5.50/2.10  tff(c_3878, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_3858, c_18])).
% 5.50/2.10  tff(c_3891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3626, c_3878])).
% 5.50/2.10  tff(c_3893, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3625])).
% 5.50/2.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.50/2.10  tff(c_2476, plain, (![C_264, B_265, A_266]: (v1_xboole_0(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(B_265, A_266))) | ~v1_xboole_0(A_266))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.50/2.10  tff(c_2487, plain, (![C_264]: (v1_xboole_0(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2476])).
% 5.50/2.10  tff(c_2519, plain, (![C_269]: (v1_xboole_0(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2487])).
% 5.50/2.10  tff(c_2532, plain, (![A_7]: (v1_xboole_0(A_7) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2519])).
% 5.50/2.10  tff(c_3905, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_3893, c_2532])).
% 5.50/2.10  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.50/2.10  tff(c_3917, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3905, c_4])).
% 5.50/2.10  tff(c_3028, plain, (![A_328, B_329]: (v1_funct_2(A_328, k1_xboole_0, B_329) | k1_relset_1(k1_xboole_0, B_329, A_328)!=k1_xboole_0 | ~r1_tarski(A_328, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2898])).
% 5.50/2.10  tff(c_3037, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_1')!=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_3028, c_2457])).
% 5.50/2.10  tff(c_3057, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3037])).
% 5.50/2.10  tff(c_3249, plain, (![C_348, B_349]: (m1_subset_1(C_348, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_348), B_349) | ~r1_tarski(k1_relat_1(C_348), k1_xboole_0) | ~v1_relat_1(C_348))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2770])).
% 5.50/2.10  tff(c_3255, plain, (![B_349]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, B_349) | ~r1_tarski(k1_relat_1('#skF_1'), k1_xboole_0) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2438, c_3249])).
% 5.50/2.10  tff(c_3268, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_164, c_2439, c_164, c_3255])).
% 5.50/2.10  tff(c_3289, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_3268, c_18])).
% 5.50/2.10  tff(c_3302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3057, c_3289])).
% 5.50/2.10  tff(c_3304, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3037])).
% 5.50/2.10  tff(c_3316, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_3304, c_2532])).
% 5.50/2.10  tff(c_3328, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3316, c_4])).
% 5.50/2.10  tff(c_3355, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3328, c_2439])).
% 5.50/2.10  tff(c_2562, plain, (![A_278, B_279, C_280]: (k1_relset_1(A_278, B_279, C_280)=k1_relat_1(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_2583, plain, (![A_278, B_279]: (k1_relset_1(A_278, B_279, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2562])).
% 5.50/2.10  tff(c_2904, plain, (![B_314]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_314) | k1_relset_1(k1_xboole_0, B_314, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_57, c_2898])).
% 5.50/2.10  tff(c_2910, plain, (![B_314]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_314) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2583, c_2904])).
% 5.50/2.10  tff(c_2913, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2910])).
% 5.50/2.10  tff(c_3337, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3328, c_3328, c_2913])).
% 5.50/2.10  tff(c_3419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3355, c_3337])).
% 5.50/2.10  tff(c_3420, plain, (![B_314]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_314))), inference(splitRight, [status(thm)], [c_2910])).
% 5.50/2.10  tff(c_3927, plain, (![B_314]: (v1_funct_2('#skF_1', '#skF_1', B_314))), inference(demodulation, [status(thm), theory('equality')], [c_3917, c_3917, c_3420])).
% 5.50/2.10  tff(c_3943, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3917, c_3917, c_2457])).
% 5.50/2.10  tff(c_4050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3927, c_3943])).
% 5.50/2.10  tff(c_4051, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_54])).
% 5.50/2.10  tff(c_4376, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4362, c_4051])).
% 5.50/2.10  tff(c_4393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4110, c_4110, c_4376])).
% 5.50/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.10  
% 5.50/2.10  Inference rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Ref     : 0
% 5.50/2.10  #Sup     : 966
% 5.50/2.10  #Fact    : 0
% 5.50/2.10  #Define  : 0
% 5.50/2.10  #Split   : 9
% 5.50/2.10  #Chain   : 0
% 5.50/2.10  #Close   : 0
% 5.50/2.10  
% 5.50/2.10  Ordering : KBO
% 5.50/2.10  
% 5.50/2.10  Simplification rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Subsume      : 211
% 5.50/2.10  #Demod        : 727
% 5.50/2.10  #Tautology    : 443
% 5.50/2.10  #SimpNegUnit  : 20
% 5.50/2.10  #BackRed      : 82
% 5.50/2.10  
% 5.50/2.10  #Partial instantiations: 0
% 5.50/2.10  #Strategies tried      : 1
% 5.50/2.10  
% 5.50/2.10  Timing (in seconds)
% 5.50/2.10  ----------------------
% 5.50/2.10  Preprocessing        : 0.34
% 5.50/2.10  Parsing              : 0.19
% 5.50/2.10  CNF conversion       : 0.02
% 5.50/2.10  Main loop            : 0.88
% 5.50/2.10  Inferencing          : 0.30
% 5.50/2.10  Reduction            : 0.27
% 5.50/2.10  Demodulation         : 0.19
% 5.50/2.10  BG Simplification    : 0.04
% 5.50/2.10  Subsumption          : 0.21
% 5.50/2.10  Abstraction          : 0.05
% 5.50/2.10  MUC search           : 0.00
% 5.50/2.10  Cooper               : 0.00
% 5.50/2.10  Total                : 1.27
% 5.50/2.10  Index Insertion      : 0.00
% 5.50/2.10  Index Deletion       : 0.00
% 5.50/2.10  Index Matching       : 0.00
% 5.50/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
