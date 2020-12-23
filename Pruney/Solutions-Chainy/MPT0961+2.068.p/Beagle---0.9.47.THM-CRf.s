%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 357 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 853 expanded)
%              Number of equality atoms :   54 ( 337 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_65,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_239,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63)))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(A_61,k1_zfmisc_1(B_62))
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] :
      ( r1_tarski(A_4,k2_zfmisc_1(k1_relat_1(A_4),k2_relat_1(A_4)))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_25,B_26,A_27] :
      ( k1_relset_1(A_25,B_26,A_27) = k1_relat_1(A_27)
      | ~ r1_tarski(A_27,k2_zfmisc_1(A_25,B_26)) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_78,plain,(
    ! [A_4] :
      ( k1_relset_1(k1_relat_1(A_4),k2_relat_1(A_4),A_4) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_42,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_48,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_154,plain,(
    ! [B_44,C_45,A_46] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_46,B_44)
      | k1_relset_1(A_46,B_44,C_45) != A_46
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,(
    ! [B_47,A_48,A_49] :
      ( k1_xboole_0 = B_47
      | v1_funct_2(A_48,A_49,B_47)
      | k1_relset_1(A_49,B_47,A_48) != A_49
      | ~ r1_tarski(A_48,k2_zfmisc_1(A_49,B_47)) ) ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_205,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | v1_funct_2(A_60,k1_relat_1(A_60),k2_relat_1(A_60))
      | k1_relset_1(k1_relat_1(A_60),k2_relat_1(A_60),A_60) != k1_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_49,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_212,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_205,c_49])).

tff(c_219,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_212])).

tff(c_220,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_219])).

tff(c_223,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_223])).

tff(c_228,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_237,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_230,c_228])).

tff(c_242,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_239,c_237])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_242])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_252,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_37,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_47,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_249,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_47])).

tff(c_16,plain,(
    ! [A_9] :
      ( v1_funct_2(k1_xboole_0,A_9,k1_xboole_0)
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_9,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_290,plain,(
    ! [A_70] :
      ( v1_funct_2('#skF_1',A_70,'#skF_1')
      | A_70 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_70,'#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_247,c_247,c_247,c_247,c_16])).

tff(c_293,plain,(
    ! [A_70] :
      ( v1_funct_2('#skF_1',A_70,'#skF_1')
      | A_70 = '#skF_1'
      | ~ r1_tarski('#skF_1',k2_zfmisc_1(A_70,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_297,plain,(
    ! [A_71] :
      ( v1_funct_2('#skF_1',A_71,'#skF_1')
      | A_71 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_293])).

tff(c_248,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_257,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_248])).

tff(c_276,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_257,c_34])).

tff(c_277,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_300,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_297,c_277])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_300])).

tff(c_305,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_320])).

tff(c_325,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_330,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_2])).

tff(c_326,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_335,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_326])).

tff(c_377,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_383,plain,(
    ! [A_85,B_86,A_87] :
      ( k1_relset_1(A_85,B_86,A_87) = k1_relat_1(A_87)
      | ~ r1_tarski(A_87,k2_zfmisc_1(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_6,c_377])).

tff(c_390,plain,(
    ! [A_85,B_86] : k1_relset_1(A_85,B_86,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_383])).

tff(c_393,plain,(
    ! [A_85,B_86] : k1_relset_1(A_85,B_86,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_390])).

tff(c_20,plain,(
    ! [C_11,B_10] :
      ( v1_funct_2(C_11,k1_xboole_0,B_10)
      | k1_relset_1(k1_xboole_0,B_10,C_11) != k1_xboole_0
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_449,plain,(
    ! [C_97,B_98] :
      ( v1_funct_2(C_97,'#skF_1',B_98)
      | k1_relset_1('#skF_1',B_98,C_97) != '#skF_1'
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_98))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_325,c_325,c_325,c_20])).

tff(c_462,plain,(
    ! [A_101,B_102] :
      ( v1_funct_2(A_101,'#skF_1',B_102)
      | k1_relset_1('#skF_1',B_102,A_101) != '#skF_1'
      | ~ r1_tarski(A_101,k2_zfmisc_1('#skF_1',B_102)) ) ),
    inference(resolution,[status(thm)],[c_6,c_449])).

tff(c_466,plain,(
    ! [B_102] :
      ( v1_funct_2('#skF_1','#skF_1',B_102)
      | k1_relset_1('#skF_1',B_102,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_330,c_462])).

tff(c_469,plain,(
    ! [B_102] : v1_funct_2('#skF_1','#skF_1',B_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_466])).

tff(c_374,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_34])).

tff(c_375,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_375])).

tff(c_473,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_484,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_473])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.31  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.14/1.31  
% 2.14/1.31  %Foreground sorts:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Background operators:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Foreground operators:
% 2.14/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.31  
% 2.48/1.32  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.48/1.32  tff(f_35, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.48/1.32  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.32  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.48/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.48/1.32  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.48/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.48/1.32  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.32  tff(c_239, plain, (![A_63]: (r1_tarski(A_63, k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63))) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.32  tff(c_230, plain, (![A_61, B_62]: (m1_subset_1(A_61, k1_zfmisc_1(B_62)) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.32  tff(c_8, plain, (![A_4]: (r1_tarski(A_4, k2_zfmisc_1(k1_relat_1(A_4), k2_relat_1(A_4))) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.32  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.32  tff(c_63, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.32  tff(c_70, plain, (![A_25, B_26, A_27]: (k1_relset_1(A_25, B_26, A_27)=k1_relat_1(A_27) | ~r1_tarski(A_27, k2_zfmisc_1(A_25, B_26)))), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.48/1.32  tff(c_78, plain, (![A_4]: (k1_relset_1(k1_relat_1(A_4), k2_relat_1(A_4), A_4)=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_8, c_70])).
% 2.48/1.32  tff(c_42, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.32  tff(c_46, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_42])).
% 2.48/1.32  tff(c_48, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.48/1.32  tff(c_154, plain, (![B_44, C_45, A_46]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_46, B_44) | k1_relset_1(A_46, B_44, C_45)!=A_46 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.32  tff(c_160, plain, (![B_47, A_48, A_49]: (k1_xboole_0=B_47 | v1_funct_2(A_48, A_49, B_47) | k1_relset_1(A_49, B_47, A_48)!=A_49 | ~r1_tarski(A_48, k2_zfmisc_1(A_49, B_47)))), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.48/1.32  tff(c_205, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | v1_funct_2(A_60, k1_relat_1(A_60), k2_relat_1(A_60)) | k1_relset_1(k1_relat_1(A_60), k2_relat_1(A_60), A_60)!=k1_relat_1(A_60) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_8, c_160])).
% 2.48/1.32  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.32  tff(c_28, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.32  tff(c_34, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 2.48/1.32  tff(c_49, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.48/1.32  tff(c_212, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_205, c_49])).
% 2.48/1.32  tff(c_219, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_212])).
% 2.48/1.32  tff(c_220, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_219])).
% 2.48/1.32  tff(c_223, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_220])).
% 2.48/1.32  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_223])).
% 2.48/1.32  tff(c_228, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_34])).
% 2.48/1.32  tff(c_237, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_230, c_228])).
% 2.48/1.32  tff(c_242, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_239, c_237])).
% 2.48/1.32  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_242])).
% 2.48/1.32  tff(c_247, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 2.48/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.32  tff(c_252, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_2])).
% 2.48/1.32  tff(c_37, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.32  tff(c_41, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32, c_37])).
% 2.48/1.32  tff(c_47, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_41])).
% 2.48/1.32  tff(c_249, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_47])).
% 2.48/1.32  tff(c_16, plain, (![A_9]: (v1_funct_2(k1_xboole_0, A_9, k1_xboole_0) | k1_xboole_0=A_9 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_9, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.32  tff(c_290, plain, (![A_70]: (v1_funct_2('#skF_1', A_70, '#skF_1') | A_70='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_70, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_247, c_247, c_247, c_247, c_16])).
% 2.48/1.32  tff(c_293, plain, (![A_70]: (v1_funct_2('#skF_1', A_70, '#skF_1') | A_70='#skF_1' | ~r1_tarski('#skF_1', k2_zfmisc_1(A_70, '#skF_1')))), inference(resolution, [status(thm)], [c_6, c_290])).
% 2.48/1.32  tff(c_297, plain, (![A_71]: (v1_funct_2('#skF_1', A_71, '#skF_1') | A_71='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_293])).
% 2.48/1.32  tff(c_248, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.48/1.32  tff(c_257, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_248])).
% 2.48/1.32  tff(c_276, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_257, c_34])).
% 2.48/1.32  tff(c_277, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_276])).
% 2.48/1.32  tff(c_300, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_297, c_277])).
% 2.48/1.32  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_300])).
% 2.48/1.32  tff(c_305, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_1')))), inference(splitRight, [status(thm)], [c_276])).
% 2.48/1.32  tff(c_320, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_305])).
% 2.48/1.32  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_320])).
% 2.48/1.32  tff(c_325, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_41])).
% 2.48/1.32  tff(c_330, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_2])).
% 2.48/1.32  tff(c_326, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_41])).
% 2.48/1.32  tff(c_335, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_325, c_326])).
% 2.48/1.32  tff(c_377, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.32  tff(c_383, plain, (![A_85, B_86, A_87]: (k1_relset_1(A_85, B_86, A_87)=k1_relat_1(A_87) | ~r1_tarski(A_87, k2_zfmisc_1(A_85, B_86)))), inference(resolution, [status(thm)], [c_6, c_377])).
% 2.48/1.32  tff(c_390, plain, (![A_85, B_86]: (k1_relset_1(A_85, B_86, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_330, c_383])).
% 2.48/1.32  tff(c_393, plain, (![A_85, B_86]: (k1_relset_1(A_85, B_86, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_390])).
% 2.48/1.32  tff(c_20, plain, (![C_11, B_10]: (v1_funct_2(C_11, k1_xboole_0, B_10) | k1_relset_1(k1_xboole_0, B_10, C_11)!=k1_xboole_0 | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_10))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.32  tff(c_449, plain, (![C_97, B_98]: (v1_funct_2(C_97, '#skF_1', B_98) | k1_relset_1('#skF_1', B_98, C_97)!='#skF_1' | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_98))))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_325, c_325, c_325, c_20])).
% 2.48/1.32  tff(c_462, plain, (![A_101, B_102]: (v1_funct_2(A_101, '#skF_1', B_102) | k1_relset_1('#skF_1', B_102, A_101)!='#skF_1' | ~r1_tarski(A_101, k2_zfmisc_1('#skF_1', B_102)))), inference(resolution, [status(thm)], [c_6, c_449])).
% 2.48/1.32  tff(c_466, plain, (![B_102]: (v1_funct_2('#skF_1', '#skF_1', B_102) | k1_relset_1('#skF_1', B_102, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_330, c_462])).
% 2.48/1.32  tff(c_469, plain, (![B_102]: (v1_funct_2('#skF_1', '#skF_1', B_102))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_466])).
% 2.48/1.32  tff(c_374, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_34])).
% 2.48/1.32  tff(c_375, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_374])).
% 2.48/1.32  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_375])).
% 2.48/1.32  tff(c_473, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_374])).
% 2.48/1.32  tff(c_484, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_473])).
% 2.48/1.32  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_330, c_484])).
% 2.48/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  Inference rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Ref     : 0
% 2.48/1.32  #Sup     : 75
% 2.48/1.32  #Fact    : 0
% 2.48/1.32  #Define  : 0
% 2.48/1.32  #Split   : 7
% 2.48/1.32  #Chain   : 0
% 2.48/1.32  #Close   : 0
% 2.48/1.32  
% 2.48/1.32  Ordering : KBO
% 2.48/1.32  
% 2.48/1.32  Simplification rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Subsume      : 9
% 2.48/1.32  #Demod        : 73
% 2.48/1.32  #Tautology    : 37
% 2.48/1.32  #SimpNegUnit  : 3
% 2.48/1.32  #BackRed      : 8
% 2.48/1.32  
% 2.48/1.32  #Partial instantiations: 0
% 2.48/1.32  #Strategies tried      : 1
% 2.48/1.32  
% 2.48/1.32  Timing (in seconds)
% 2.48/1.32  ----------------------
% 2.48/1.33  Preprocessing        : 0.29
% 2.48/1.33  Parsing              : 0.15
% 2.48/1.33  CNF conversion       : 0.02
% 2.48/1.33  Main loop            : 0.25
% 2.48/1.33  Inferencing          : 0.10
% 2.48/1.33  Reduction            : 0.07
% 2.48/1.33  Demodulation         : 0.05
% 2.48/1.33  BG Simplification    : 0.02
% 2.48/1.33  Subsumption          : 0.04
% 2.48/1.33  Abstraction          : 0.01
% 2.48/1.33  MUC search           : 0.00
% 2.48/1.33  Cooper               : 0.00
% 2.48/1.33  Total                : 0.57
% 2.48/1.33  Index Insertion      : 0.00
% 2.48/1.33  Index Deletion       : 0.00
% 2.48/1.33  Index Matching       : 0.00
% 2.48/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
