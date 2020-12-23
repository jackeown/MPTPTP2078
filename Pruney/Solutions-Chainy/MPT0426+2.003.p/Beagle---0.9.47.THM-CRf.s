%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 272 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 684 expanded)
%              Number of equality atoms :   63 ( 220 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_36,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_68,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_396,plain,(
    ! [A_69,B_70] :
      ( k6_setfam_1(A_69,B_70) = k1_setfam_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_404,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_396])).

tff(c_443,plain,(
    ! [A_76,B_77] :
      ( k8_setfam_1(A_76,B_77) = k6_setfam_1(A_76,B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_446,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_443])).

tff(c_452,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_446])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_10,plain,(
    ! [A_5] : k1_subset_1(A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_14,plain,(
    ! [A_7] :
      ( k8_setfam_1(A_7,k1_xboole_0) = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_7] : k8_setfam_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14])).

tff(c_473,plain,(
    ! [A_7] : k8_setfam_1(A_7,'#skF_7') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_60])).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_111])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_569])).

tff(c_573,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_575,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_111])).

tff(c_574,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_587,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_1'(A_92,k1_setfam_1(A_92),C_93),A_92)
      | r2_hidden(C_93,k1_setfam_1(A_92))
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_32)
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_164,plain,(
    ! [C_48,D_49,A_50] :
      ( r2_hidden(C_48,D_49)
      | ~ r2_hidden(D_49,A_50)
      | ~ r2_hidden(C_48,k1_setfam_1(A_50))
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_172,plain,(
    ! [C_48] :
      ( r2_hidden(C_48,'#skF_8')
      | ~ r2_hidden(C_48,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_124,c_164])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_38,B_39] : ~ r2_hidden(A_38,k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_229,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_107])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_124])).

tff(c_285,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_141,plain,(
    ! [A_45,B_46] :
      ( k6_setfam_1(A_45,B_46) = k1_setfam_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_141])).

tff(c_357,plain,(
    ! [A_64,B_65] :
      ( k8_setfam_1(A_64,B_65) = k6_setfam_1(A_64,B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_360,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_357])).

tff(c_366,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_360])).

tff(c_367,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_366])).

tff(c_371,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_111])).

tff(c_287,plain,(
    ! [A_60,C_61] :
      ( r2_hidden('#skF_1'(A_60,k1_setfam_1(A_60),C_61),A_60)
      | r2_hidden(C_61,k1_setfam_1(A_60))
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ! [D_32] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_32)
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_32)
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_127,plain,(
    ! [D_43] :
      ( r2_hidden('#skF_6',D_43)
      | ~ r2_hidden(D_43,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_56])).

tff(c_129,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_124,c_127])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_129])).

tff(c_134,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_6',D_32)
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_300,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_61))
      | r2_hidden(C_61,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_287,c_134])).

tff(c_382,plain,(
    ! [C_67] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_67))
      | r2_hidden(C_67,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_300])).

tff(c_32,plain,(
    ! [C_21,A_9] :
      ( ~ r2_hidden(C_21,'#skF_1'(A_9,k1_setfam_1(A_9),C_21))
      | r2_hidden(C_21,k1_setfam_1(A_9))
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_386,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_382,c_32])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_285,c_371,c_386])).

tff(c_393,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_6',D_32)
      | ~ r2_hidden(D_32,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_596,plain,(
    ! [C_93] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_93))
      | r2_hidden(C_93,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_587,c_393])).

tff(c_616,plain,(
    ! [C_94] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_94))
      | r2_hidden(C_94,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_596])).

tff(c_620,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_616,c_32])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_574,c_575,c_620])).

tff(c_628,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_631,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_46])).

tff(c_627,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_667,plain,(
    ! [C_101,D_102,A_103] :
      ( r2_hidden(C_101,D_102)
      | ~ r2_hidden(D_102,A_103)
      | ~ r2_hidden(C_101,k1_setfam_1(A_103))
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_675,plain,(
    ! [C_101] :
      ( r2_hidden(C_101,'#skF_8')
      | ~ r2_hidden(C_101,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_627,c_667])).

tff(c_677,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_734,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_107])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_734,c_627])).

tff(c_762,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_644,plain,(
    ! [A_98,B_99] :
      ( k6_setfam_1(A_98,B_99) = k1_setfam_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_652,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_644])).

tff(c_827,plain,(
    ! [A_114,B_115] :
      ( k8_setfam_1(A_114,B_115) = k6_setfam_1(A_114,B_115)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_830,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_827])).

tff(c_836,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_830])).

tff(c_837,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_836])).

tff(c_841,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_628])).

tff(c_761,plain,(
    ! [C_101] :
      ( r2_hidden(C_101,'#skF_8')
      | ~ r2_hidden(C_101,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_848,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_841,c_761])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:50:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.45  
% 2.61/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.46  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 2.61/1.46  
% 2.61/1.46  %Foreground sorts:
% 2.61/1.46  
% 2.61/1.46  
% 2.61/1.46  %Background operators:
% 2.61/1.46  
% 2.61/1.46  
% 2.61/1.46  %Foreground operators:
% 2.61/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.46  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.61/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.61/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.46  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.61/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.46  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.61/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.46  
% 2.95/1.48  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.95/1.48  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.95/1.48  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.95/1.48  tff(f_36, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.95/1.48  tff(f_38, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.95/1.48  tff(f_68, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.95/1.48  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.95/1.48  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.95/1.48  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_396, plain, (![A_69, B_70]: (k6_setfam_1(A_69, B_70)=k1_setfam_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.95/1.48  tff(c_404, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_396])).
% 2.95/1.48  tff(c_443, plain, (![A_76, B_77]: (k8_setfam_1(A_76, B_77)=k6_setfam_1(A_76, B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.48  tff(c_446, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_443])).
% 2.95/1.48  tff(c_452, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_404, c_446])).
% 2.95/1.48  tff(c_456, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_452])).
% 2.95/1.48  tff(c_10, plain, (![A_5]: (k1_subset_1(A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.95/1.48  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.95/1.48  tff(c_58, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.95/1.48  tff(c_14, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.48  tff(c_60, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14])).
% 2.95/1.48  tff(c_473, plain, (![A_7]: (k8_setfam_1(A_7, '#skF_7')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_60])).
% 2.95/1.48  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_111, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.95/1.48  tff(c_569, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_111])).
% 2.95/1.48  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_569])).
% 2.95/1.48  tff(c_573, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_452])).
% 2.95/1.48  tff(c_575, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_111])).
% 2.95/1.48  tff(c_574, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_452])).
% 2.95/1.48  tff(c_587, plain, (![A_92, C_93]: (r2_hidden('#skF_1'(A_92, k1_setfam_1(A_92), C_93), A_92) | r2_hidden(C_93, k1_setfam_1(A_92)) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.48  tff(c_54, plain, (![D_32]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_32) | ~r2_hidden(D_32, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_124, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 2.95/1.48  tff(c_164, plain, (![C_48, D_49, A_50]: (r2_hidden(C_48, D_49) | ~r2_hidden(D_49, A_50) | ~r2_hidden(C_48, k1_setfam_1(A_50)) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.48  tff(c_172, plain, (![C_48]: (r2_hidden(C_48, '#skF_8') | ~r2_hidden(C_48, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_124, c_164])).
% 2.95/1.48  tff(c_223, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_172])).
% 2.95/1.48  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.48  tff(c_104, plain, (![A_38, B_39]: (~r2_hidden(A_38, k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.95/1.48  tff(c_107, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_104])).
% 2.95/1.48  tff(c_229, plain, (![A_1]: (~r2_hidden(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_107])).
% 2.95/1.48  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_124])).
% 2.95/1.48  tff(c_285, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_172])).
% 2.95/1.48  tff(c_141, plain, (![A_45, B_46]: (k6_setfam_1(A_45, B_46)=k1_setfam_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.95/1.48  tff(c_149, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_141])).
% 2.95/1.48  tff(c_357, plain, (![A_64, B_65]: (k8_setfam_1(A_64, B_65)=k6_setfam_1(A_64, B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.48  tff(c_360, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_357])).
% 2.95/1.48  tff(c_366, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_360])).
% 2.95/1.48  tff(c_367, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_285, c_366])).
% 2.95/1.48  tff(c_371, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_111])).
% 2.95/1.48  tff(c_287, plain, (![A_60, C_61]: (r2_hidden('#skF_1'(A_60, k1_setfam_1(A_60), C_61), A_60) | r2_hidden(C_61, k1_setfam_1(A_60)) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.48  tff(c_52, plain, (![D_32]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_32) | ~r2_hidden(D_32, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_125, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 2.95/1.48  tff(c_56, plain, (![D_32]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_32) | ~r2_hidden(D_32, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_127, plain, (![D_43]: (r2_hidden('#skF_6', D_43) | ~r2_hidden(D_43, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_111, c_56])).
% 2.95/1.48  tff(c_129, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_124, c_127])).
% 2.95/1.48  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_129])).
% 2.95/1.48  tff(c_134, plain, (![D_32]: (r2_hidden('#skF_6', D_32) | ~r2_hidden(D_32, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 2.95/1.48  tff(c_300, plain, (![C_61]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_61)) | r2_hidden(C_61, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_287, c_134])).
% 2.95/1.48  tff(c_382, plain, (![C_67]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_67)) | r2_hidden(C_67, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_285, c_300])).
% 2.95/1.48  tff(c_32, plain, (![C_21, A_9]: (~r2_hidden(C_21, '#skF_1'(A_9, k1_setfam_1(A_9), C_21)) | r2_hidden(C_21, k1_setfam_1(A_9)) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.48  tff(c_386, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_382, c_32])).
% 2.95/1.48  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_285, c_371, c_386])).
% 2.95/1.48  tff(c_393, plain, (![D_32]: (r2_hidden('#skF_6', D_32) | ~r2_hidden(D_32, '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 2.95/1.48  tff(c_596, plain, (![C_93]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_93)) | r2_hidden(C_93, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_587, c_393])).
% 2.95/1.48  tff(c_616, plain, (![C_94]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_94)) | r2_hidden(C_94, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_574, c_596])).
% 2.95/1.48  tff(c_620, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_616, c_32])).
% 2.95/1.48  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_574, c_575, c_620])).
% 2.95/1.48  tff(c_628, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 2.95/1.48  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.95/1.48  tff(c_631, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_46])).
% 2.95/1.48  tff(c_627, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 2.95/1.48  tff(c_667, plain, (![C_101, D_102, A_103]: (r2_hidden(C_101, D_102) | ~r2_hidden(D_102, A_103) | ~r2_hidden(C_101, k1_setfam_1(A_103)) | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.48  tff(c_675, plain, (![C_101]: (r2_hidden(C_101, '#skF_8') | ~r2_hidden(C_101, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_627, c_667])).
% 2.95/1.48  tff(c_677, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_675])).
% 2.95/1.48  tff(c_734, plain, (![A_1]: (~r2_hidden(A_1, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_107])).
% 2.95/1.48  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_734, c_627])).
% 2.95/1.48  tff(c_762, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_675])).
% 2.95/1.48  tff(c_644, plain, (![A_98, B_99]: (k6_setfam_1(A_98, B_99)=k1_setfam_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.95/1.48  tff(c_652, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_644])).
% 2.95/1.48  tff(c_827, plain, (![A_114, B_115]: (k8_setfam_1(A_114, B_115)=k6_setfam_1(A_114, B_115) | k1_xboole_0=B_115 | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(A_114))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.48  tff(c_830, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_44, c_827])).
% 2.95/1.48  tff(c_836, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_830])).
% 2.95/1.48  tff(c_837, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_762, c_836])).
% 2.95/1.48  tff(c_841, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_628])).
% 2.95/1.48  tff(c_761, plain, (![C_101]: (r2_hidden(C_101, '#skF_8') | ~r2_hidden(C_101, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_675])).
% 2.95/1.48  tff(c_848, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_841, c_761])).
% 2.95/1.48  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_631, c_848])).
% 2.95/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  Inference rules
% 2.95/1.48  ----------------------
% 2.95/1.48  #Ref     : 0
% 2.95/1.48  #Sup     : 157
% 2.95/1.48  #Fact    : 0
% 2.95/1.48  #Define  : 0
% 2.95/1.48  #Split   : 14
% 2.95/1.48  #Chain   : 0
% 2.95/1.48  #Close   : 0
% 2.95/1.48  
% 2.95/1.48  Ordering : KBO
% 2.95/1.48  
% 2.95/1.48  Simplification rules
% 2.95/1.48  ----------------------
% 2.95/1.48  #Subsume      : 12
% 2.95/1.48  #Demod        : 216
% 2.95/1.48  #Tautology    : 123
% 2.95/1.48  #SimpNegUnit  : 30
% 2.95/1.48  #BackRed      : 124
% 2.95/1.48  
% 2.95/1.48  #Partial instantiations: 0
% 2.95/1.48  #Strategies tried      : 1
% 2.95/1.48  
% 2.95/1.48  Timing (in seconds)
% 2.95/1.48  ----------------------
% 2.95/1.48  Preprocessing        : 0.34
% 2.95/1.48  Parsing              : 0.17
% 2.95/1.48  CNF conversion       : 0.03
% 2.95/1.48  Main loop            : 0.33
% 2.95/1.48  Inferencing          : 0.10
% 2.95/1.48  Reduction            : 0.12
% 2.95/1.48  Demodulation         : 0.08
% 2.95/1.48  BG Simplification    : 0.02
% 2.95/1.48  Subsumption          : 0.06
% 2.95/1.48  Abstraction          : 0.02
% 2.95/1.48  MUC search           : 0.00
% 2.95/1.48  Cooper               : 0.00
% 2.95/1.48  Total                : 0.71
% 2.95/1.48  Index Insertion      : 0.00
% 2.95/1.48  Index Deletion       : 0.00
% 2.95/1.48  Index Matching       : 0.00
% 2.95/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
