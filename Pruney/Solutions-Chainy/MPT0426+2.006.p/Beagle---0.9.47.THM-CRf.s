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
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 267 expanded)
%              Number of leaves         :   26 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 635 expanded)
%              Number of equality atoms :   57 ( 205 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_342,plain,(
    ! [A_83,B_84] :
      ( k6_setfam_1(A_83,B_84) = k1_setfam_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_350,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_342])).

tff(c_422,plain,(
    ! [A_94,B_95] :
      ( k8_setfam_1(A_94,B_95) = k6_setfam_1(A_94,B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_425,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_422])).

tff(c_431,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_425])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] :
      ( k8_setfam_1(A_2,k1_xboole_0) = A_2
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [A_2] : k8_setfam_1(A_2,k1_xboole_0) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_442,plain,(
    ! [A_2] : k8_setfam_1(A_2,'#skF_7') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_55])).

tff(c_44,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_495,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_70])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_495])).

tff(c_499,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_501,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_70])).

tff(c_500,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_507,plain,(
    ! [A_101,C_102] :
      ( r2_hidden('#skF_1'(A_101,k1_setfam_1(A_101),C_102),A_101)
      | r2_hidden(C_102,k1_setfam_1(A_101))
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_222,plain,(
    ! [A_66,B_67] :
      ( k8_setfam_1(A_66,B_67) = k6_setfam_1(A_66,B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_222])).

tff(c_231,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_225])).

tff(c_235,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_243,plain,(
    ! [A_2] : k8_setfam_1(A_2,'#skF_7') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_55])).

tff(c_282,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_70])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_282])).

tff(c_287,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_185,plain,(
    ! [A_62,C_63] :
      ( r2_hidden('#skF_1'(A_62,k1_setfam_1(A_62),C_63),A_62)
      | r2_hidden(C_63,k1_setfam_1(A_62))
      | k1_xboole_0 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    ! [D_33] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_105,plain,(
    ! [D_43] :
      ( r2_hidden('#skF_6',D_43)
      | ~ r2_hidden(D_43,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_52])).

tff(c_107,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_107])).

tff(c_112,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_211,plain,(
    ! [C_63] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_63))
      | r2_hidden(C_63,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_185,c_112])).

tff(c_289,plain,(
    ! [C_73] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_73))
      | r2_hidden(C_73,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_211])).

tff(c_24,plain,(
    ! [C_16,A_4] :
      ( ~ r2_hidden(C_16,'#skF_1'(A_4,k1_setfam_1(A_4),C_16))
      | r2_hidden(C_16,k1_setfam_1(A_4))
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_293,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_289,c_24])).

tff(c_300,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_293])).

tff(c_286,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_309,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_70])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_309])).

tff(c_313,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_526,plain,(
    ! [C_102] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_102))
      | r2_hidden(C_102,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_507,c_313])).

tff(c_540,plain,(
    ! [C_102] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_102))
      | r2_hidden(C_102,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_526])).

tff(c_551,plain,(
    ! [C_104,A_105] :
      ( ~ r2_hidden(C_104,'#skF_1'(A_105,k1_setfam_1(A_105),C_104))
      | r2_hidden(C_104,k1_setfam_1(A_105))
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_555,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_540,c_551])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_500,c_501,c_555])).

tff(c_564,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_566,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_42])).

tff(c_563,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_627,plain,(
    ! [C_119,D_120,A_121] :
      ( r2_hidden(C_119,D_120)
      | ~ r2_hidden(D_120,A_121)
      | ~ r2_hidden(C_119,k1_setfam_1(A_121))
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_635,plain,(
    ! [C_119] :
      ( r2_hidden(C_119,'#skF_8')
      | ~ r2_hidden(C_119,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_563,c_627])).

tff(c_659,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_568,plain,(
    ! [C_106,B_107,A_108] :
      ( ~ v1_xboole_0(C_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(C_106))
      | ~ r2_hidden(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_574,plain,(
    ! [A_1,A_108] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_108,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_568])).

tff(c_575,plain,(
    ! [A_108] : ~ r2_hidden(A_108,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_664,plain,(
    ! [A_108] : ~ r2_hidden(A_108,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_575])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_563])).

tff(c_683,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_578,plain,(
    ! [A_110,B_111] :
      ( k6_setfam_1(A_110,B_111) = k1_setfam_1(B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k1_zfmisc_1(A_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_586,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_578])).

tff(c_716,plain,(
    ! [A_128,B_129] :
      ( k8_setfam_1(A_128,B_129) = k6_setfam_1(A_128,B_129)
      | k1_xboole_0 = B_129
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(A_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_719,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_716])).

tff(c_725,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_719])).

tff(c_726,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_725])).

tff(c_731,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_564])).

tff(c_682,plain,(
    ! [C_119] :
      ( r2_hidden(C_119,'#skF_8')
      | ~ r2_hidden(C_119,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_738,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_731,c_682])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_738])).

tff(c_747,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.49  
% 2.91/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.49  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 2.91/1.49  
% 2.91/1.49  %Foreground sorts:
% 2.91/1.49  
% 2.91/1.49  
% 2.91/1.49  %Background operators:
% 2.91/1.49  
% 2.91/1.49  
% 2.91/1.49  %Foreground operators:
% 2.91/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.49  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.91/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.91/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.91/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.49  tff('#skF_8', type, '#skF_8': $i).
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.49  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.91/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.91/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.91/1.49  
% 2.91/1.51  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.91/1.51  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.91/1.51  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.91/1.51  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.51  tff(f_58, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.91/1.51  tff(f_75, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.91/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.91/1.51  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_342, plain, (![A_83, B_84]: (k6_setfam_1(A_83, B_84)=k1_setfam_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.51  tff(c_350, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_342])).
% 2.91/1.51  tff(c_422, plain, (![A_94, B_95]: (k8_setfam_1(A_94, B_95)=k6_setfam_1(A_94, B_95) | k1_xboole_0=B_95 | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.51  tff(c_425, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_422])).
% 2.91/1.51  tff(c_431, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_425])).
% 2.91/1.51  tff(c_435, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_431])).
% 2.91/1.51  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.91/1.51  tff(c_6, plain, (![A_2]: (k8_setfam_1(A_2, k1_xboole_0)=A_2 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.51  tff(c_55, plain, (![A_2]: (k8_setfam_1(A_2, k1_xboole_0)=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.91/1.51  tff(c_442, plain, (![A_2]: (k8_setfam_1(A_2, '#skF_7')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_55])).
% 2.91/1.51  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_70, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.91/1.51  tff(c_495, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_70])).
% 2.91/1.51  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_495])).
% 2.91/1.51  tff(c_499, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_431])).
% 2.91/1.51  tff(c_501, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_70])).
% 2.91/1.51  tff(c_500, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_431])).
% 2.91/1.51  tff(c_507, plain, (![A_101, C_102]: (r2_hidden('#skF_1'(A_101, k1_setfam_1(A_101), C_102), A_101) | r2_hidden(C_102, k1_setfam_1(A_101)) | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.51  tff(c_124, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.51  tff(c_132, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_124])).
% 2.91/1.51  tff(c_222, plain, (![A_66, B_67]: (k8_setfam_1(A_66, B_67)=k6_setfam_1(A_66, B_67) | k1_xboole_0=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.51  tff(c_225, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_222])).
% 2.91/1.51  tff(c_231, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_225])).
% 2.91/1.51  tff(c_235, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_231])).
% 2.91/1.51  tff(c_243, plain, (![A_2]: (k8_setfam_1(A_2, '#skF_7')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_235, c_55])).
% 2.91/1.51  tff(c_282, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_70])).
% 2.91/1.51  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_282])).
% 2.91/1.51  tff(c_287, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_231])).
% 2.91/1.51  tff(c_185, plain, (![A_62, C_63]: (r2_hidden('#skF_1'(A_62, k1_setfam_1(A_62), C_63), A_62) | r2_hidden(C_63, k1_setfam_1(A_62)) | k1_xboole_0=A_62)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.51  tff(c_48, plain, (![D_33]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_71, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 2.91/1.51  tff(c_50, plain, (![D_33]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 2.91/1.51  tff(c_52, plain, (![D_33]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_105, plain, (![D_43]: (r2_hidden('#skF_6', D_43) | ~r2_hidden(D_43, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_52])).
% 2.91/1.51  tff(c_107, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_105])).
% 2.91/1.51  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_107])).
% 2.91/1.51  tff(c_112, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 2.91/1.51  tff(c_211, plain, (![C_63]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_63)) | r2_hidden(C_63, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_185, c_112])).
% 2.91/1.51  tff(c_289, plain, (![C_73]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_73)) | r2_hidden(C_73, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_287, c_211])).
% 2.91/1.51  tff(c_24, plain, (![C_16, A_4]: (~r2_hidden(C_16, '#skF_1'(A_4, k1_setfam_1(A_4), C_16)) | r2_hidden(C_16, k1_setfam_1(A_4)) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.51  tff(c_293, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_289, c_24])).
% 2.91/1.51  tff(c_300, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_287, c_293])).
% 2.91/1.51  tff(c_286, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_231])).
% 2.91/1.51  tff(c_309, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_70])).
% 2.91/1.51  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_309])).
% 2.91/1.51  tff(c_313, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 2.91/1.51  tff(c_526, plain, (![C_102]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_102)) | r2_hidden(C_102, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_507, c_313])).
% 2.91/1.51  tff(c_540, plain, (![C_102]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_102)) | r2_hidden(C_102, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_500, c_526])).
% 2.91/1.51  tff(c_551, plain, (![C_104, A_105]: (~r2_hidden(C_104, '#skF_1'(A_105, k1_setfam_1(A_105), C_104)) | r2_hidden(C_104, k1_setfam_1(A_105)) | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.51  tff(c_555, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_540, c_551])).
% 2.91/1.51  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_500, c_501, c_555])).
% 2.91/1.51  tff(c_564, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 2.91/1.51  tff(c_42, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.51  tff(c_566, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_42])).
% 2.91/1.51  tff(c_563, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.91/1.51  tff(c_627, plain, (![C_119, D_120, A_121]: (r2_hidden(C_119, D_120) | ~r2_hidden(D_120, A_121) | ~r2_hidden(C_119, k1_setfam_1(A_121)) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.51  tff(c_635, plain, (![C_119]: (r2_hidden(C_119, '#skF_8') | ~r2_hidden(C_119, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_563, c_627])).
% 2.91/1.51  tff(c_659, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_635])).
% 2.91/1.51  tff(c_568, plain, (![C_106, B_107, A_108]: (~v1_xboole_0(C_106) | ~m1_subset_1(B_107, k1_zfmisc_1(C_106)) | ~r2_hidden(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.91/1.51  tff(c_574, plain, (![A_1, A_108]: (~v1_xboole_0(A_1) | ~r2_hidden(A_108, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_568])).
% 2.91/1.51  tff(c_575, plain, (![A_108]: (~r2_hidden(A_108, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_574])).
% 2.91/1.51  tff(c_664, plain, (![A_108]: (~r2_hidden(A_108, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_575])).
% 2.91/1.51  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_563])).
% 2.91/1.51  tff(c_683, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_635])).
% 2.91/1.51  tff(c_578, plain, (![A_110, B_111]: (k6_setfam_1(A_110, B_111)=k1_setfam_1(B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k1_zfmisc_1(A_110))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.91/1.51  tff(c_586, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_578])).
% 2.91/1.51  tff(c_716, plain, (![A_128, B_129]: (k8_setfam_1(A_128, B_129)=k6_setfam_1(A_128, B_129) | k1_xboole_0=B_129 | ~m1_subset_1(B_129, k1_zfmisc_1(k1_zfmisc_1(A_128))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.51  tff(c_719, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_40, c_716])).
% 2.91/1.51  tff(c_725, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_719])).
% 2.91/1.51  tff(c_726, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_683, c_725])).
% 2.91/1.51  tff(c_731, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_726, c_564])).
% 2.91/1.51  tff(c_682, plain, (![C_119]: (r2_hidden(C_119, '#skF_8') | ~r2_hidden(C_119, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_635])).
% 2.91/1.51  tff(c_738, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_731, c_682])).
% 2.91/1.51  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_738])).
% 2.91/1.51  tff(c_747, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_574])).
% 2.91/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.91/1.51  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_747, c_2])).
% 2.91/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.51  
% 2.91/1.51  Inference rules
% 2.91/1.51  ----------------------
% 2.91/1.51  #Ref     : 0
% 2.91/1.51  #Sup     : 134
% 2.91/1.51  #Fact    : 0
% 2.91/1.51  #Define  : 0
% 2.91/1.51  #Split   : 27
% 2.91/1.51  #Chain   : 0
% 2.91/1.51  #Close   : 0
% 2.91/1.51  
% 2.91/1.51  Ordering : KBO
% 2.91/1.51  
% 2.91/1.51  Simplification rules
% 2.91/1.51  ----------------------
% 2.91/1.51  #Subsume      : 28
% 2.91/1.51  #Demod        : 125
% 2.91/1.51  #Tautology    : 67
% 2.91/1.51  #SimpNegUnit  : 27
% 2.91/1.51  #BackRed      : 72
% 2.91/1.51  
% 2.91/1.51  #Partial instantiations: 0
% 2.91/1.51  #Strategies tried      : 1
% 2.91/1.51  
% 2.91/1.51  Timing (in seconds)
% 2.91/1.51  ----------------------
% 2.91/1.51  Preprocessing        : 0.33
% 2.91/1.51  Parsing              : 0.17
% 2.91/1.51  CNF conversion       : 0.02
% 2.91/1.51  Main loop            : 0.33
% 2.91/1.51  Inferencing          : 0.11
% 2.91/1.51  Reduction            : 0.11
% 2.91/1.51  Demodulation         : 0.07
% 2.91/1.51  BG Simplification    : 0.02
% 2.91/1.51  Subsumption          : 0.06
% 2.91/1.51  Abstraction          : 0.02
% 2.91/1.51  MUC search           : 0.00
% 2.91/1.51  Cooper               : 0.00
% 2.91/1.51  Total                : 0.70
% 2.91/1.51  Index Insertion      : 0.00
% 2.91/1.51  Index Deletion       : 0.00
% 2.91/1.51  Index Matching       : 0.00
% 2.91/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
