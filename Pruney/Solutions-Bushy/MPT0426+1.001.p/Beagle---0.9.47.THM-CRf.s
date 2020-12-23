%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0426+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:17 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 275 expanded)
%              Number of leaves         :   27 (  97 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 678 expanded)
%              Number of equality atoms :   60 ( 208 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_55,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_36,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_249,plain,(
    ! [A_54,B_55] :
      ( k6_setfam_1(A_54,B_55) = k1_setfam_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_253,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_249])).

tff(c_321,plain,(
    ! [A_66,B_67] :
      ( k8_setfam_1(A_66,B_67) = k6_setfam_1(A_66,B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_324,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_38,c_321])).

tff(c_326,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_324])).

tff(c_327,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_2,plain,(
    ! [A_1] :
      ( k8_setfam_1(A_1,k1_xboole_0) = A_1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_363,plain,(
    ! [A_71] :
      ( k8_setfam_1(A_71,'#skF_7') = A_71
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_2])).

tff(c_367,plain,(
    k8_setfam_1('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_363])).

tff(c_42,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_368,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_76])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_368])).

tff(c_372,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_76])).

tff(c_373,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_293,plain,(
    ! [A_62,C_63] :
      ( r2_hidden('#skF_1'(A_62,k1_setfam_1(A_62),C_63),A_62)
      | r2_hidden(C_63,k1_setfam_1(A_62))
      | k1_xboole_0 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [D_29] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_29)
      | ~ r2_hidden(D_29,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_34])).

tff(c_118,plain,(
    ! [C_40,D_41,A_42] :
      ( r2_hidden(C_40,D_41)
      | ~ r2_hidden(D_41,A_42)
      | ~ r2_hidden(C_40,k1_setfam_1(A_42))
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    ! [C_40] :
      ( r2_hidden(C_40,'#skF_8')
      | ~ r2_hidden(C_40,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_78,c_118])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_28,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_144,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_61])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_144])).

tff(c_151,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_174,plain,(
    ! [A_48,C_49] :
      ( r2_hidden('#skF_1'(A_48,k1_setfam_1(A_48),C_49),A_48)
      | r2_hidden(C_49,k1_setfam_1(A_48))
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    ! [D_29] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_29)
      | ~ r2_hidden(D_29,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,(
    ! [D_29] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_29)
      | ~ r2_hidden(D_29,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    ! [D_36] :
      ( r2_hidden('#skF_6',D_36)
      | ~ r2_hidden(D_36,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_50])).

tff(c_92,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_90])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_92])).

tff(c_97,plain,(
    ! [D_29] :
      ( r2_hidden('#skF_6',D_29)
      | ~ r2_hidden(D_29,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_191,plain,(
    ! [C_49] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_49))
      | r2_hidden(C_49,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_174,c_97])).

tff(c_208,plain,(
    ! [C_50] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_50))
      | r2_hidden(C_50,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_191])).

tff(c_20,plain,(
    ! [C_15,A_3] :
      ( ~ r2_hidden(C_15,'#skF_1'(A_3,k1_setfam_1(A_3),C_15))
      | r2_hidden(C_15,k1_setfam_1(A_3))
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_208,c_20])).

tff(c_220,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_212])).

tff(c_108,plain,(
    ! [A_38,B_39] :
      ( k6_setfam_1(A_38,B_39) = k1_setfam_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_235,plain,(
    ! [A_51,B_52] :
      ( k8_setfam_1(A_51,B_52) = k6_setfam_1(A_51,B_52)
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_38,c_235])).

tff(c_240,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_238])).

tff(c_241,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_240])).

tff(c_242,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_76])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_242])).

tff(c_246,plain,(
    ! [D_29] :
      ( r2_hidden('#skF_6',D_29)
      | ~ r2_hidden(D_29,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_311,plain,(
    ! [C_63] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_63))
      | r2_hidden(C_63,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_293,c_246])).

tff(c_381,plain,(
    ! [C_74] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_74))
      | r2_hidden(C_74,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_311])).

tff(c_385,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_381,c_20])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_373,c_374,c_385])).

tff(c_396,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_401,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_401])).

tff(c_408,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_395,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_400,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_395,c_34])).

tff(c_427,plain,(
    ! [C_78,D_79,A_80] :
      ( r2_hidden(C_78,D_79)
      | ~ r2_hidden(D_79,A_80)
      | ~ r2_hidden(C_78,k1_setfam_1(A_80))
      | k1_xboole_0 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_435,plain,(
    ! [C_78] :
      ( r2_hidden(C_78,'#skF_8')
      | ~ r2_hidden(C_78,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_395,c_427])).

tff(c_437,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_440,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_61])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_440])).

tff(c_447,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_417,plain,(
    ! [A_76,B_77] :
      ( k6_setfam_1(A_76,B_77) = k1_setfam_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_421,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_417])).

tff(c_491,plain,(
    ! [A_87,B_88] :
      ( k8_setfam_1(A_87,B_88) = k6_setfam_1(A_87,B_88)
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_494,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_38,c_491])).

tff(c_496,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_494])).

tff(c_497,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_496])).

tff(c_409,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_499,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_409])).

tff(c_446,plain,(
    ! [C_78] :
      ( r2_hidden(C_78,'#skF_8')
      | ~ r2_hidden(C_78,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_506,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_499,c_446])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_506])).

%------------------------------------------------------------------------------
