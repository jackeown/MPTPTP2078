%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 294 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :    8
%              Number of atoms          :  164 ( 750 expanded)
%              Number of equality atoms :   61 ( 230 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_295,plain,(
    ! [A_71,B_72] :
      ( k6_setfam_1(A_71,B_72) = k1_setfam_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_295])).

tff(c_348,plain,(
    ! [A_85,B_86] :
      ( k8_setfam_1(A_85,B_86) = k6_setfam_1(A_85,B_86)
      | k1_xboole_0 = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_351,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_52,c_348])).

tff(c_353,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_351])).

tff(c_354,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_22,plain,(
    ! [A_8] :
      ( k8_setfam_1(A_8,k1_xboole_0) = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_431,plain,(
    ! [A_92] :
      ( k8_setfam_1(A_92,'#skF_9') = A_92
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_354,c_22])).

tff(c_435,plain,(
    k8_setfam_1('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52,c_431])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_436,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_81])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_436])).

tff(c_440,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_481,plain,(
    ~ r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_81])).

tff(c_441,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_442,plain,(
    ! [A_93,C_94] :
      ( r2_hidden('#skF_3'(A_93,k1_setfam_1(A_93),C_94),A_93)
      | r2_hidden(C_94,k1_setfam_1(A_93))
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_10','#skF_9')
      | r2_hidden('#skF_8',D_33)
      | ~ r2_hidden(D_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_149,plain,(
    ! [C_56,D_57,A_58] :
      ( r2_hidden(C_56,D_57)
      | ~ r2_hidden(D_57,A_58)
      | ~ r2_hidden(C_56,k1_setfam_1(A_58))
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_160,plain,(
    ! [C_56] :
      ( r2_hidden(C_56,'#skF_10')
      | ~ r2_hidden(C_56,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_90,c_149])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [D_35,B_36,A_37] :
      ( ~ r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k4_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [D_35,A_7] :
      ( ~ r2_hidden(D_35,A_7)
      | ~ r2_hidden(D_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_90,c_80])).

tff(c_182,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_93])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_182])).

tff(c_191,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_123,plain,(
    ! [A_48,B_49] :
      ( k6_setfam_1(A_48,B_49) = k1_setfam_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_127,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_192,plain,(
    ! [A_60,B_61] :
      ( k8_setfam_1(A_60,B_61) = k6_setfam_1(A_60,B_61)
      | k1_xboole_0 = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_52,c_192])).

tff(c_197,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_195])).

tff(c_198,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_197])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_81])).

tff(c_223,plain,(
    ! [A_64,C_65] :
      ( r2_hidden('#skF_3'(A_64,k1_setfam_1(A_64),C_65),A_64)
      | r2_hidden(C_65,k1_setfam_1(A_64))
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_60,plain,(
    ! [D_33] :
      ( ~ r2_hidden('#skF_8','#skF_10')
      | r2_hidden('#skF_8',D_33)
      | ~ r2_hidden(D_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_64,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9'))
      | r2_hidden('#skF_8',D_33)
      | ~ r2_hidden(D_33,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,(
    ! [D_46] :
      ( r2_hidden('#skF_8',D_46)
      | ~ r2_hidden(D_46,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_64])).

tff(c_108,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_90,c_106])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_108])).

tff(c_113,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8',D_33)
      | ~ r2_hidden(D_33,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_243,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_65))
      | r2_hidden(C_65,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_223,c_113])).

tff(c_266,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_65))
      | r2_hidden(C_65,k1_setfam_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_243])).

tff(c_279,plain,(
    ! [C_67,A_68] :
      ( ~ r2_hidden(C_67,'#skF_3'(A_68,k1_setfam_1(A_68),C_67))
      | r2_hidden(C_67,k1_setfam_1(A_68))
      | k1_xboole_0 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_283,plain,
    ( k1_xboole_0 = '#skF_9'
    | r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_266,c_279])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_191,c_199,c_283])).

tff(c_291,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8',D_33)
      | ~ r2_hidden(D_33,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_454,plain,(
    ! [C_94] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_94))
      | r2_hidden(C_94,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_442,c_291])).

tff(c_486,plain,(
    ! [C_95] :
      ( r2_hidden('#skF_8','#skF_3'('#skF_9',k1_setfam_1('#skF_9'),C_95))
      | r2_hidden(C_95,k1_setfam_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_454])).

tff(c_40,plain,(
    ! [C_22,A_10] :
      ( ~ r2_hidden(C_22,'#skF_3'(A_10,k1_setfam_1(A_10),C_22))
      | r2_hidden(C_22,k1_setfam_1(A_10))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_490,plain,
    ( k1_xboole_0 = '#skF_9'
    | r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_486,c_40])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_481,c_441,c_481,c_490])).

tff(c_499,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_500,plain,(
    r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( r2_hidden('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_501,plain,(
    ~ r2_hidden('#skF_8',k8_setfam_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_501])).

tff(c_504,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_549,plain,(
    ! [C_110,D_111,A_112] :
      ( r2_hidden(C_110,D_111)
      | ~ r2_hidden(D_111,A_112)
      | ~ r2_hidden(C_110,k1_setfam_1(A_112))
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_560,plain,(
    ! [C_110] :
      ( r2_hidden(C_110,'#skF_10')
      | ~ r2_hidden(C_110,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_504,c_549])).

tff(c_562,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_507,plain,(
    ! [D_96,A_97] :
      ( ~ r2_hidden(D_96,A_97)
      | ~ r2_hidden(D_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_515,plain,(
    ~ r2_hidden('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_504,c_507])).

tff(c_566,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_515])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_566])).

tff(c_575,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_523,plain,(
    ! [A_102,B_103] :
      ( k6_setfam_1(A_102,B_103) = k1_setfam_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_527,plain,(
    k6_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_523])).

tff(c_577,plain,(
    ! [A_114,B_115] :
      ( k8_setfam_1(A_114,B_115) = k6_setfam_1(A_114,B_115)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_580,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k6_setfam_1('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_52,c_577])).

tff(c_582,plain,
    ( k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_580])).

tff(c_583,plain,(
    k8_setfam_1('#skF_7','#skF_9') = k1_setfam_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_582])).

tff(c_584,plain,(
    r2_hidden('#skF_8',k1_setfam_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_500])).

tff(c_574,plain,(
    ! [C_110] :
      ( r2_hidden(C_110,'#skF_10')
      | ~ r2_hidden(C_110,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_591,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_584,c_574])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.52/1.36  
% 2.52/1.36  %Foreground sorts:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Background operators:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Foreground operators:
% 2.52/1.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.52/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.36  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.52/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.52/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.52/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.52/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.52/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.52/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.52/1.36  
% 2.70/1.38  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.70/1.38  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.70/1.38  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.70/1.38  tff(f_67, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.70/1.38  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.70/1.38  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.70/1.38  tff(c_50, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_295, plain, (![A_71, B_72]: (k6_setfam_1(A_71, B_72)=k1_setfam_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.38  tff(c_299, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_295])).
% 2.70/1.38  tff(c_348, plain, (![A_85, B_86]: (k8_setfam_1(A_85, B_86)=k6_setfam_1(A_85, B_86) | k1_xboole_0=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.38  tff(c_351, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_52, c_348])).
% 2.70/1.38  tff(c_353, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_351])).
% 2.70/1.38  tff(c_354, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_353])).
% 2.70/1.38  tff(c_22, plain, (![A_8]: (k8_setfam_1(A_8, k1_xboole_0)=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.38  tff(c_431, plain, (![A_92]: (k8_setfam_1(A_92, '#skF_9')=A_92 | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_354, c_22])).
% 2.70/1.38  tff(c_435, plain, (k8_setfam_1('#skF_7', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_52, c_431])).
% 2.70/1.38  tff(c_54, plain, (~r2_hidden('#skF_8', '#skF_10') | ~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_81, plain, (~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.70/1.38  tff(c_436, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_81])).
% 2.70/1.38  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_436])).
% 2.70/1.38  tff(c_440, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(splitRight, [status(thm)], [c_353])).
% 2.70/1.38  tff(c_481, plain, (~r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_81])).
% 2.70/1.38  tff(c_441, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_353])).
% 2.70/1.38  tff(c_442, plain, (![A_93, C_94]: (r2_hidden('#skF_3'(A_93, k1_setfam_1(A_93), C_94), A_93) | r2_hidden(C_94, k1_setfam_1(A_93)) | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_62, plain, (![D_33]: (r2_hidden('#skF_10', '#skF_9') | r2_hidden('#skF_8', D_33) | ~r2_hidden(D_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_90, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 2.70/1.38  tff(c_149, plain, (![C_56, D_57, A_58]: (r2_hidden(C_56, D_57) | ~r2_hidden(D_57, A_58) | ~r2_hidden(C_56, k1_setfam_1(A_58)) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_160, plain, (![C_56]: (r2_hidden(C_56, '#skF_10') | ~r2_hidden(C_56, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_90, c_149])).
% 2.70/1.38  tff(c_177, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_160])).
% 2.70/1.38  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.38  tff(c_77, plain, (![D_35, B_36, A_37]: (~r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k4_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.38  tff(c_80, plain, (![D_35, A_7]: (~r2_hidden(D_35, A_7) | ~r2_hidden(D_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_77])).
% 2.70/1.38  tff(c_93, plain, (~r2_hidden('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_90, c_80])).
% 2.70/1.38  tff(c_182, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_93])).
% 2.70/1.38  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_182])).
% 2.70/1.38  tff(c_191, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_160])).
% 2.70/1.38  tff(c_123, plain, (![A_48, B_49]: (k6_setfam_1(A_48, B_49)=k1_setfam_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.38  tff(c_127, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_123])).
% 2.70/1.38  tff(c_192, plain, (![A_60, B_61]: (k8_setfam_1(A_60, B_61)=k6_setfam_1(A_60, B_61) | k1_xboole_0=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.38  tff(c_195, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_52, c_192])).
% 2.70/1.38  tff(c_197, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_195])).
% 2.70/1.38  tff(c_198, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_191, c_197])).
% 2.70/1.38  tff(c_199, plain, (~r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_81])).
% 2.70/1.38  tff(c_223, plain, (![A_64, C_65]: (r2_hidden('#skF_3'(A_64, k1_setfam_1(A_64), C_65), A_64) | r2_hidden(C_65, k1_setfam_1(A_64)) | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_60, plain, (![D_33]: (~r2_hidden('#skF_8', '#skF_10') | r2_hidden('#skF_8', D_33) | ~r2_hidden(D_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_95, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_60])).
% 2.70/1.38  tff(c_64, plain, (![D_33]: (r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9')) | r2_hidden('#skF_8', D_33) | ~r2_hidden(D_33, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_106, plain, (![D_46]: (r2_hidden('#skF_8', D_46) | ~r2_hidden(D_46, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_81, c_64])).
% 2.70/1.38  tff(c_108, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_90, c_106])).
% 2.70/1.38  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_108])).
% 2.70/1.38  tff(c_113, plain, (![D_33]: (r2_hidden('#skF_8', D_33) | ~r2_hidden(D_33, '#skF_9'))), inference(splitRight, [status(thm)], [c_60])).
% 2.70/1.38  tff(c_243, plain, (![C_65]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_65)) | r2_hidden(C_65, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_223, c_113])).
% 2.70/1.38  tff(c_266, plain, (![C_65]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_65)) | r2_hidden(C_65, k1_setfam_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_191, c_243])).
% 2.70/1.38  tff(c_279, plain, (![C_67, A_68]: (~r2_hidden(C_67, '#skF_3'(A_68, k1_setfam_1(A_68), C_67)) | r2_hidden(C_67, k1_setfam_1(A_68)) | k1_xboole_0=A_68)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_283, plain, (k1_xboole_0='#skF_9' | r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(resolution, [status(thm)], [c_266, c_279])).
% 2.70/1.38  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_191, c_199, c_283])).
% 2.70/1.38  tff(c_291, plain, (![D_33]: (r2_hidden('#skF_8', D_33) | ~r2_hidden(D_33, '#skF_9'))), inference(splitRight, [status(thm)], [c_62])).
% 2.70/1.38  tff(c_454, plain, (![C_94]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_94)) | r2_hidden(C_94, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_442, c_291])).
% 2.70/1.38  tff(c_486, plain, (![C_95]: (r2_hidden('#skF_8', '#skF_3'('#skF_9', k1_setfam_1('#skF_9'), C_95)) | r2_hidden(C_95, k1_setfam_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_441, c_454])).
% 2.70/1.38  tff(c_40, plain, (![C_22, A_10]: (~r2_hidden(C_22, '#skF_3'(A_10, k1_setfam_1(A_10), C_22)) | r2_hidden(C_22, k1_setfam_1(A_10)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_490, plain, (k1_xboole_0='#skF_9' | r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(resolution, [status(thm)], [c_486, c_40])).
% 2.70/1.38  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_481, c_441, c_481, c_490])).
% 2.70/1.38  tff(c_499, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_54])).
% 2.70/1.38  tff(c_500, plain, (r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_54])).
% 2.70/1.38  tff(c_56, plain, (r2_hidden('#skF_10', '#skF_9') | ~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_501, plain, (~r2_hidden('#skF_8', k8_setfam_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.70/1.38  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_500, c_501])).
% 2.70/1.38  tff(c_504, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_56])).
% 2.70/1.38  tff(c_549, plain, (![C_110, D_111, A_112]: (r2_hidden(C_110, D_111) | ~r2_hidden(D_111, A_112) | ~r2_hidden(C_110, k1_setfam_1(A_112)) | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.38  tff(c_560, plain, (![C_110]: (r2_hidden(C_110, '#skF_10') | ~r2_hidden(C_110, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_504, c_549])).
% 2.70/1.38  tff(c_562, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_560])).
% 2.70/1.38  tff(c_507, plain, (![D_96, A_97]: (~r2_hidden(D_96, A_97) | ~r2_hidden(D_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_77])).
% 2.70/1.38  tff(c_515, plain, (~r2_hidden('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_504, c_507])).
% 2.70/1.38  tff(c_566, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_515])).
% 2.70/1.38  tff(c_573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_504, c_566])).
% 2.70/1.38  tff(c_575, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_560])).
% 2.70/1.38  tff(c_523, plain, (![A_102, B_103]: (k6_setfam_1(A_102, B_103)=k1_setfam_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_102))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.38  tff(c_527, plain, (k6_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_523])).
% 2.70/1.38  tff(c_577, plain, (![A_114, B_115]: (k8_setfam_1(A_114, B_115)=k6_setfam_1(A_114, B_115) | k1_xboole_0=B_115 | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(A_114))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.38  tff(c_580, plain, (k8_setfam_1('#skF_7', '#skF_9')=k6_setfam_1('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_52, c_577])).
% 2.70/1.38  tff(c_582, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9') | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_580])).
% 2.70/1.38  tff(c_583, plain, (k8_setfam_1('#skF_7', '#skF_9')=k1_setfam_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_575, c_582])).
% 2.70/1.38  tff(c_584, plain, (r2_hidden('#skF_8', k1_setfam_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_500])).
% 2.70/1.38  tff(c_574, plain, (![C_110]: (r2_hidden(C_110, '#skF_10') | ~r2_hidden(C_110, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_560])).
% 2.70/1.38  tff(c_591, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_584, c_574])).
% 2.70/1.38  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_591])).
% 2.70/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  Inference rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Ref     : 0
% 2.70/1.38  #Sup     : 107
% 2.70/1.38  #Fact    : 0
% 2.70/1.38  #Define  : 0
% 2.70/1.38  #Split   : 10
% 2.70/1.38  #Chain   : 0
% 2.70/1.38  #Close   : 0
% 2.70/1.38  
% 2.70/1.38  Ordering : KBO
% 2.70/1.38  
% 2.70/1.38  Simplification rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Subsume      : 10
% 2.70/1.38  #Demod        : 102
% 2.70/1.38  #Tautology    : 52
% 2.70/1.38  #SimpNegUnit  : 11
% 2.70/1.38  #BackRed      : 58
% 2.70/1.38  
% 2.70/1.38  #Partial instantiations: 0
% 2.70/1.38  #Strategies tried      : 1
% 2.70/1.38  
% 2.70/1.38  Timing (in seconds)
% 2.70/1.38  ----------------------
% 2.70/1.38  Preprocessing        : 0.31
% 2.70/1.38  Parsing              : 0.15
% 2.70/1.38  CNF conversion       : 0.02
% 2.70/1.38  Main loop            : 0.29
% 2.70/1.38  Inferencing          : 0.09
% 2.70/1.38  Reduction            : 0.09
% 2.70/1.38  Demodulation         : 0.06
% 2.70/1.38  BG Simplification    : 0.02
% 2.70/1.38  Subsumption          : 0.06
% 2.70/1.38  Abstraction          : 0.02
% 2.70/1.38  MUC search           : 0.00
% 2.70/1.38  Cooper               : 0.00
% 2.70/1.38  Total                : 0.65
% 2.70/1.38  Index Insertion      : 0.00
% 2.70/1.38  Index Deletion       : 0.00
% 2.70/1.38  Index Matching       : 0.00
% 2.70/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
