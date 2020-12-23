%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 337 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :    8
%              Number of atoms          :  175 ( 810 expanded)
%              Number of equality atoms :   71 ( 277 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
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

tff(c_36,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_411,plain,(
    ! [A_65,B_66] :
      ( k6_setfam_1(A_65,B_66) = k1_setfam_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_415,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_411])).

tff(c_467,plain,(
    ! [A_77,B_78] :
      ( k8_setfam_1(A_77,B_78) = k6_setfam_1(A_77,B_78)
      | k1_xboole_0 = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_470,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_467])).

tff(c_472,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_470])).

tff(c_473,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_8,plain,(
    ! [A_5] :
      ( k8_setfam_1(A_5,k1_xboole_0) = A_5
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_554,plain,(
    ! [A_84] :
      ( k8_setfam_1(A_84,'#skF_8') = A_84
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_8])).

tff(c_558,plain,(
    k8_setfam_1('#skF_6','#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_554])).

tff(c_42,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_559,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_66])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_559])).

tff(c_564,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_9','#skF_8')
      | r2_hidden('#skF_7',D_30)
      | ~ r2_hidden(D_30,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_67,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_116,plain,(
    ! [A_39,B_40] :
      ( k6_setfam_1(A_39,B_40) = k1_setfam_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_157,plain,(
    ! [A_45,B_46] :
      ( k8_setfam_1(A_45,B_46) = k6_setfam_1(A_45,B_46)
      | k1_xboole_0 = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_160,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_162,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_160])).

tff(c_163,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_169,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_6])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_169])).

tff(c_172,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_66])).

tff(c_173,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_250,plain,(
    ! [A_52,C_53] :
      ( r2_hidden('#skF_2'(A_52,k1_setfam_1(A_52),C_53),A_52)
      | r2_hidden(C_53,k1_setfam_1(A_52))
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8'))
      | r2_hidden('#skF_7',D_30)
      | ~ r2_hidden(D_30,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_96,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_7',D_30)
      | ~ r2_hidden(D_30,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50])).

tff(c_271,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_7','#skF_2'('#skF_8',k1_setfam_1('#skF_8'),C_53))
      | r2_hidden(C_53,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_250,c_96])).

tff(c_285,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_7','#skF_2'('#skF_8',k1_setfam_1('#skF_8'),C_53))
      | r2_hidden(C_53,k1_setfam_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_271])).

tff(c_389,plain,(
    ! [C_61,A_62] :
      ( ~ r2_hidden(C_61,'#skF_2'(A_62,k1_setfam_1(A_62),C_61))
      | r2_hidden(C_61,k1_setfam_1(A_62))
      | k1_xboole_0 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_393,plain,
    ( k1_xboole_0 = '#skF_8'
    | r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_285,c_389])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_173,c_181,c_393])).

tff(c_403,plain,(
    ! [D_63] :
      ( r2_hidden('#skF_7',D_63)
      | ~ r2_hidden(D_63,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_407,plain,
    ( r2_hidden('#skF_7','#skF_1'('#skF_8'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_403])).

tff(c_408,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_565,plain,(
    ! [A_85,C_86] :
      ( r2_hidden('#skF_2'(A_85,k1_setfam_1(A_85),C_86),A_85)
      | r2_hidden(C_86,k1_setfam_1(A_85))
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_599,plain,(
    ! [A_87,C_88] :
      ( ~ v1_xboole_0(A_87)
      | r2_hidden(C_88,k1_setfam_1(A_87))
      | k1_xboole_0 = A_87 ) ),
    inference(resolution,[status(thm)],[c_565,c_2])).

tff(c_563,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_594,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_66])).

tff(c_602,plain,
    ( ~ v1_xboole_0('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_599,c_594])).

tff(c_620,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_602])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_620])).

tff(c_624,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_630,plain,(
    ! [A_90,B_91] :
      ( k6_setfam_1(A_90,B_91) = k1_setfam_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_634,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_630])).

tff(c_714,plain,(
    ! [A_101,B_102] :
      ( k8_setfam_1(A_101,B_102) = k6_setfam_1(A_101,B_102)
      | k1_xboole_0 = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_717,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_714])).

tff(c_719,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_717])).

tff(c_720,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_719])).

tff(c_728,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_6])).

tff(c_730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_728])).

tff(c_731,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_739,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_66])).

tff(c_732,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_719])).

tff(c_744,plain,(
    ! [A_105,C_106] :
      ( r2_hidden('#skF_2'(A_105,k1_setfam_1(A_105),C_106),A_105)
      | r2_hidden(C_106,k1_setfam_1(A_105))
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_401,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_7',D_30)
      | ~ r2_hidden(D_30,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_761,plain,(
    ! [C_106] :
      ( r2_hidden('#skF_7','#skF_2'('#skF_8',k1_setfam_1('#skF_8'),C_106))
      | r2_hidden(C_106,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_744,c_401])).

tff(c_830,plain,(
    ! [C_110] :
      ( r2_hidden('#skF_7','#skF_2'('#skF_8',k1_setfam_1('#skF_8'),C_110))
      | r2_hidden(C_110,k1_setfam_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_761])).

tff(c_26,plain,(
    ! [C_19,A_7] :
      ( ~ r2_hidden(C_19,'#skF_2'(A_7,k1_setfam_1(A_7),C_19))
      | r2_hidden(C_19,k1_setfam_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_834,plain,
    ( k1_xboole_0 = '#skF_8'
    | r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_830,c_26])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_732,c_739,c_834])).

tff(c_845,plain,(
    r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_855,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_40])).

tff(c_844,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_849,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_844,c_2])).

tff(c_868,plain,(
    ! [C_114,D_115,A_116] :
      ( r2_hidden(C_114,D_115)
      | ~ r2_hidden(D_115,A_116)
      | ~ r2_hidden(C_114,k1_setfam_1(A_116))
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_878,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,'#skF_9')
      | ~ r2_hidden(C_114,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_844,c_868])).

tff(c_915,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_923,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_6])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_923])).

tff(c_927,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_858,plain,(
    ! [A_112,B_113] :
      ( k6_setfam_1(A_112,B_113) = k1_setfam_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_862,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_858])).

tff(c_1003,plain,(
    ! [A_126,B_127] :
      ( k8_setfam_1(A_126,B_127) = k6_setfam_1(A_126,B_127)
      | k1_xboole_0 = B_127
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1006,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_1003])).

tff(c_1008,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_1006])).

tff(c_1009,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_927,c_1008])).

tff(c_1016,plain,(
    r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_845])).

tff(c_926,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,'#skF_9')
      | ~ r2_hidden(C_114,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_1023,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_1016,c_926])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_855,c_1023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:09:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.60  
% 2.87/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.60  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 2.87/1.60  
% 2.87/1.60  %Foreground sorts:
% 2.87/1.60  
% 2.87/1.60  
% 2.87/1.60  %Background operators:
% 2.87/1.60  
% 2.87/1.60  
% 2.87/1.60  %Foreground operators:
% 2.87/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.60  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.87/1.60  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.60  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.60  tff('#skF_9', type, '#skF_9': $i).
% 2.87/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.60  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.60  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.87/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.87/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.87/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.87/1.60  
% 2.87/1.62  tff(f_78, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.87/1.62  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.87/1.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.87/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.87/1.62  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.87/1.62  tff(f_62, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.87/1.62  tff(c_36, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_411, plain, (![A_65, B_66]: (k6_setfam_1(A_65, B_66)=k1_setfam_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.62  tff(c_415, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_411])).
% 2.87/1.62  tff(c_467, plain, (![A_77, B_78]: (k8_setfam_1(A_77, B_78)=k6_setfam_1(A_77, B_78) | k1_xboole_0=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.62  tff(c_470, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_38, c_467])).
% 2.87/1.62  tff(c_472, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_470])).
% 2.87/1.62  tff(c_473, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_472])).
% 2.87/1.62  tff(c_8, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.62  tff(c_554, plain, (![A_84]: (k8_setfam_1(A_84, '#skF_8')=A_84 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_8])).
% 2.87/1.62  tff(c_558, plain, (k8_setfam_1('#skF_6', '#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_38, c_554])).
% 2.87/1.62  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_8') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_66, plain, (~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.87/1.62  tff(c_559, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_66])).
% 2.87/1.62  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_559])).
% 2.87/1.62  tff(c_564, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_472])).
% 2.87/1.62  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.62  tff(c_48, plain, (![D_30]: (r2_hidden('#skF_9', '#skF_8') | r2_hidden('#skF_7', D_30) | ~r2_hidden(D_30, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_67, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 2.87/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.62  tff(c_71, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_67, c_2])).
% 2.87/1.62  tff(c_116, plain, (![A_39, B_40]: (k6_setfam_1(A_39, B_40)=k1_setfam_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.62  tff(c_120, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_116])).
% 2.87/1.62  tff(c_157, plain, (![A_45, B_46]: (k8_setfam_1(A_45, B_46)=k6_setfam_1(A_45, B_46) | k1_xboole_0=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.62  tff(c_160, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_38, c_157])).
% 2.87/1.62  tff(c_162, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_160])).
% 2.87/1.62  tff(c_163, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_162])).
% 2.87/1.62  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.62  tff(c_169, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_6])).
% 2.87/1.62  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_169])).
% 2.87/1.62  tff(c_172, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(splitRight, [status(thm)], [c_162])).
% 2.87/1.62  tff(c_181, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_66])).
% 2.87/1.62  tff(c_173, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_162])).
% 2.87/1.62  tff(c_250, plain, (![A_52, C_53]: (r2_hidden('#skF_2'(A_52, k1_setfam_1(A_52), C_53), A_52) | r2_hidden(C_53, k1_setfam_1(A_52)) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_50, plain, (![D_30]: (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8')) | r2_hidden('#skF_7', D_30) | ~r2_hidden(D_30, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_96, plain, (![D_30]: (r2_hidden('#skF_7', D_30) | ~r2_hidden(D_30, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_50])).
% 2.87/1.62  tff(c_271, plain, (![C_53]: (r2_hidden('#skF_7', '#skF_2'('#skF_8', k1_setfam_1('#skF_8'), C_53)) | r2_hidden(C_53, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_250, c_96])).
% 2.87/1.62  tff(c_285, plain, (![C_53]: (r2_hidden('#skF_7', '#skF_2'('#skF_8', k1_setfam_1('#skF_8'), C_53)) | r2_hidden(C_53, k1_setfam_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_173, c_271])).
% 2.87/1.62  tff(c_389, plain, (![C_61, A_62]: (~r2_hidden(C_61, '#skF_2'(A_62, k1_setfam_1(A_62), C_61)) | r2_hidden(C_61, k1_setfam_1(A_62)) | k1_xboole_0=A_62)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_393, plain, (k1_xboole_0='#skF_8' | r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_285, c_389])).
% 2.87/1.62  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_173, c_181, c_393])).
% 2.87/1.62  tff(c_403, plain, (![D_63]: (r2_hidden('#skF_7', D_63) | ~r2_hidden(D_63, '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 2.87/1.62  tff(c_407, plain, (r2_hidden('#skF_7', '#skF_1'('#skF_8')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_403])).
% 2.87/1.62  tff(c_408, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_407])).
% 2.87/1.62  tff(c_565, plain, (![A_85, C_86]: (r2_hidden('#skF_2'(A_85, k1_setfam_1(A_85), C_86), A_85) | r2_hidden(C_86, k1_setfam_1(A_85)) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_599, plain, (![A_87, C_88]: (~v1_xboole_0(A_87) | r2_hidden(C_88, k1_setfam_1(A_87)) | k1_xboole_0=A_87)), inference(resolution, [status(thm)], [c_565, c_2])).
% 2.87/1.62  tff(c_563, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(splitRight, [status(thm)], [c_472])).
% 2.87/1.62  tff(c_594, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_66])).
% 2.87/1.62  tff(c_602, plain, (~v1_xboole_0('#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_599, c_594])).
% 2.87/1.62  tff(c_620, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_602])).
% 2.87/1.62  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_620])).
% 2.87/1.62  tff(c_624, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_407])).
% 2.87/1.62  tff(c_630, plain, (![A_90, B_91]: (k6_setfam_1(A_90, B_91)=k1_setfam_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.62  tff(c_634, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_630])).
% 2.87/1.62  tff(c_714, plain, (![A_101, B_102]: (k8_setfam_1(A_101, B_102)=k6_setfam_1(A_101, B_102) | k1_xboole_0=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.62  tff(c_717, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_38, c_714])).
% 2.87/1.62  tff(c_719, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_717])).
% 2.87/1.62  tff(c_720, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_719])).
% 2.87/1.62  tff(c_728, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_6])).
% 2.87/1.62  tff(c_730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_728])).
% 2.87/1.62  tff(c_731, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(splitRight, [status(thm)], [c_719])).
% 2.87/1.62  tff(c_739, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_66])).
% 2.87/1.62  tff(c_732, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_719])).
% 2.87/1.62  tff(c_744, plain, (![A_105, C_106]: (r2_hidden('#skF_2'(A_105, k1_setfam_1(A_105), C_106), A_105) | r2_hidden(C_106, k1_setfam_1(A_105)) | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_401, plain, (![D_30]: (r2_hidden('#skF_7', D_30) | ~r2_hidden(D_30, '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 2.87/1.62  tff(c_761, plain, (![C_106]: (r2_hidden('#skF_7', '#skF_2'('#skF_8', k1_setfam_1('#skF_8'), C_106)) | r2_hidden(C_106, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_744, c_401])).
% 2.87/1.62  tff(c_830, plain, (![C_110]: (r2_hidden('#skF_7', '#skF_2'('#skF_8', k1_setfam_1('#skF_8'), C_110)) | r2_hidden(C_110, k1_setfam_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_732, c_761])).
% 2.87/1.62  tff(c_26, plain, (![C_19, A_7]: (~r2_hidden(C_19, '#skF_2'(A_7, k1_setfam_1(A_7), C_19)) | r2_hidden(C_19, k1_setfam_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_834, plain, (k1_xboole_0='#skF_8' | r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_830, c_26])).
% 2.87/1.62  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_739, c_732, c_739, c_834])).
% 2.87/1.62  tff(c_845, plain, (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_42])).
% 2.87/1.62  tff(c_40, plain, (~r2_hidden('#skF_7', '#skF_9') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.62  tff(c_855, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_40])).
% 2.87/1.62  tff(c_844, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_42])).
% 2.87/1.62  tff(c_849, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_844, c_2])).
% 2.87/1.62  tff(c_868, plain, (![C_114, D_115, A_116]: (r2_hidden(C_114, D_115) | ~r2_hidden(D_115, A_116) | ~r2_hidden(C_114, k1_setfam_1(A_116)) | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.62  tff(c_878, plain, (![C_114]: (r2_hidden(C_114, '#skF_9') | ~r2_hidden(C_114, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_844, c_868])).
% 2.87/1.62  tff(c_915, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_878])).
% 2.87/1.62  tff(c_923, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_6])).
% 2.87/1.62  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_849, c_923])).
% 2.87/1.62  tff(c_927, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_878])).
% 2.87/1.62  tff(c_858, plain, (![A_112, B_113]: (k6_setfam_1(A_112, B_113)=k1_setfam_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.62  tff(c_862, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_858])).
% 2.87/1.62  tff(c_1003, plain, (![A_126, B_127]: (k8_setfam_1(A_126, B_127)=k6_setfam_1(A_126, B_127) | k1_xboole_0=B_127 | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_126))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.62  tff(c_1006, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_38, c_1003])).
% 2.87/1.62  tff(c_1008, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_1006])).
% 2.87/1.62  tff(c_1009, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_927, c_1008])).
% 2.87/1.62  tff(c_1016, plain, (r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_845])).
% 2.87/1.62  tff(c_926, plain, (![C_114]: (r2_hidden(C_114, '#skF_9') | ~r2_hidden(C_114, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_878])).
% 2.87/1.62  tff(c_1023, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_1016, c_926])).
% 2.87/1.62  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_855, c_1023])).
% 2.87/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.62  
% 2.87/1.62  Inference rules
% 2.87/1.62  ----------------------
% 2.87/1.62  #Ref     : 0
% 2.87/1.62  #Sup     : 181
% 2.87/1.62  #Fact    : 0
% 2.87/1.62  #Define  : 0
% 2.87/1.62  #Split   : 25
% 2.87/1.62  #Chain   : 0
% 2.87/1.62  #Close   : 0
% 2.87/1.62  
% 2.87/1.62  Ordering : KBO
% 2.87/1.62  
% 2.87/1.62  Simplification rules
% 2.87/1.62  ----------------------
% 2.87/1.62  #Subsume      : 28
% 2.87/1.62  #Demod        : 132
% 2.87/1.62  #Tautology    : 55
% 2.87/1.63  #SimpNegUnit  : 45
% 2.87/1.63  #BackRed      : 72
% 2.87/1.63  
% 2.87/1.63  #Partial instantiations: 0
% 2.87/1.63  #Strategies tried      : 1
% 2.87/1.63  
% 2.87/1.63  Timing (in seconds)
% 2.87/1.63  ----------------------
% 2.87/1.63  Preprocessing        : 0.40
% 2.87/1.63  Parsing              : 0.20
% 2.87/1.63  CNF conversion       : 0.03
% 2.87/1.63  Main loop            : 0.39
% 2.87/1.63  Inferencing          : 0.13
% 2.87/1.63  Reduction            : 0.12
% 2.87/1.63  Demodulation         : 0.08
% 2.87/1.63  BG Simplification    : 0.02
% 2.87/1.63  Subsumption          : 0.08
% 2.87/1.63  Abstraction          : 0.02
% 2.87/1.63  MUC search           : 0.00
% 2.87/1.63  Cooper               : 0.00
% 2.87/1.63  Total                : 0.84
% 2.87/1.63  Index Insertion      : 0.00
% 2.87/1.63  Index Deletion       : 0.00
% 2.87/1.63  Index Matching       : 0.00
% 2.87/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
