%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 161 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 319 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_42,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_65,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_72,plain,(
    ! [A_66] :
      ( k1_relat_1(A_66) = k1_xboole_0
      | k2_relat_1(A_66) != k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,
    ( k1_relat_1('#skF_8') = k1_xboole_0
    | k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_72])).

tff(c_77,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_204,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_213,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_204])).

tff(c_66,plain,(
    ! [D_65] :
      ( ~ r2_hidden(D_65,k2_relset_1('#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1(D_65,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7')
    | k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_6','#skF_7','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_225,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_110])).

tff(c_399,plain,(
    ! [A_119,C_120] :
      ( r2_hidden(k4_tarski('#skF_5'(A_119,k2_relat_1(A_119),C_120),C_120),A_119)
      | ~ r2_hidden(C_120,k2_relat_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_75,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_109,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_111,plain,(
    ! [A_76,C_77,B_78] :
      ( m1_subset_1(A_76,C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_76,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_111])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [C_70,A_71,D_72] :
      ( r2_hidden(C_70,k2_relat_1(A_71))
      | ~ r2_hidden(k4_tarski(D_72,C_70),A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_159,plain,(
    ! [C_91,B_92,D_93] :
      ( r2_hidden(C_91,k2_relat_1(B_92))
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(k4_tarski(D_93,C_91),B_92) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_162,plain,(
    ! [C_91,D_93] :
      ( r2_hidden(C_91,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k4_tarski(D_93,C_91),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_118,c_159])).

tff(c_165,plain,(
    ! [C_91,D_93] :
      ( r2_hidden(C_91,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden(k4_tarski(D_93,C_91),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_162])).

tff(c_466,plain,(
    ! [C_124] :
      ( r2_hidden(C_124,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden(C_124,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_399,c_165])).

tff(c_6,plain,(
    ! [B_4,D_6,A_3,C_5] :
      ( r2_hidden(B_4,D_6)
      | ~ r2_hidden(k4_tarski(A_3,B_4),k2_zfmisc_1(C_5,D_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_443,plain,(
    ! [C_120,D_6,C_5] :
      ( r2_hidden(C_120,D_6)
      | ~ r2_hidden(C_120,k2_relat_1(k2_zfmisc_1(C_5,D_6))) ) ),
    inference(resolution,[status(thm)],[c_399,c_6])).

tff(c_480,plain,(
    ! [C_125] :
      ( r2_hidden(C_125,'#skF_7')
      | ~ r2_hidden(C_125,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_466,c_443])).

tff(c_492,plain,
    ( r2_hidden('#skF_1'(k2_relat_1('#skF_8')),'#skF_7')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_480])).

tff(c_497,plain,(
    r2_hidden('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_492])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_500,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_8')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_497,c_10])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_500])).

tff(c_505,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_554,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_561,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_554])).

tff(c_564,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_561])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_564])).

tff(c_569,plain,(
    ! [A_143] : ~ r2_hidden(A_143,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_579,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2,c_569])).

tff(c_582,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_77])).

tff(c_585,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_2])).

tff(c_804,plain,(
    ! [A_182,C_183] :
      ( r2_hidden(k4_tarski('#skF_5'(A_182,k2_relat_1(A_182),C_183),C_183),A_182)
      | ~ r2_hidden(C_183,k2_relat_1(A_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_567,plain,(
    ! [A_75] : ~ r2_hidden(A_75,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_860,plain,(
    ! [C_188] : ~ r2_hidden(C_188,k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_804,c_567])).

tff(c_868,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_585,c_860])).

tff(c_877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_868])).

tff(c_878,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1045,plain,(
    ! [A_226,B_227,C_228] :
      ( k1_relset_1(A_226,B_227,C_228) = k1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1052,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_1045])).

tff(c_1055,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_1052])).

tff(c_1057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.52  
% 2.99/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.52  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 2.99/1.52  
% 2.99/1.52  %Foreground sorts:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Background operators:
% 2.99/1.52  
% 2.99/1.52  
% 2.99/1.52  %Foreground operators:
% 2.99/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.99/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.52  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.99/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.52  tff('#skF_8', type, '#skF_8': $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.99/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.52  
% 3.16/1.53  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.16/1.53  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.53  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.53  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.16/1.53  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.53  tff(f_70, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.16/1.53  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.16/1.53  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.16/1.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.16/1.53  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.16/1.53  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.16/1.53  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.53  tff(c_42, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.53  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.53  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.53  tff(c_56, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.16/1.53  tff(c_65, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_56])).
% 3.16/1.53  tff(c_72, plain, (![A_66]: (k1_relat_1(A_66)=k1_xboole_0 | k2_relat_1(A_66)!=k1_xboole_0 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.54  tff(c_76, plain, (k1_relat_1('#skF_8')=k1_xboole_0 | k2_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_72])).
% 3.16/1.54  tff(c_77, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 3.16/1.54  tff(c_204, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.54  tff(c_213, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_204])).
% 3.16/1.54  tff(c_66, plain, (![D_65]: (~r2_hidden(D_65, k2_relset_1('#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1(D_65, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.54  tff(c_71, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_66])).
% 3.16/1.54  tff(c_110, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_6', '#skF_7', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_71])).
% 3.16/1.54  tff(c_225, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_110])).
% 3.16/1.54  tff(c_399, plain, (![A_119, C_120]: (r2_hidden(k4_tarski('#skF_5'(A_119, k2_relat_1(A_119), C_120), C_120), A_119) | ~r2_hidden(C_120, k2_relat_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.54  tff(c_101, plain, (![C_73, B_74, A_75]: (~v1_xboole_0(C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.54  tff(c_108, plain, (![A_75]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(A_75, '#skF_8'))), inference(resolution, [status(thm)], [c_44, c_101])).
% 3.16/1.54  tff(c_109, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_108])).
% 3.16/1.54  tff(c_111, plain, (![A_76, C_77, B_78]: (m1_subset_1(A_76, C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.54  tff(c_118, plain, (![A_76]: (m1_subset_1(A_76, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(A_76, '#skF_8'))), inference(resolution, [status(thm)], [c_44, c_111])).
% 3.16/1.54  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.54  tff(c_95, plain, (![C_70, A_71, D_72]: (r2_hidden(C_70, k2_relat_1(A_71)) | ~r2_hidden(k4_tarski(D_72, C_70), A_71))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.54  tff(c_159, plain, (![C_91, B_92, D_93]: (r2_hidden(C_91, k2_relat_1(B_92)) | v1_xboole_0(B_92) | ~m1_subset_1(k4_tarski(D_93, C_91), B_92))), inference(resolution, [status(thm)], [c_12, c_95])).
% 3.16/1.54  tff(c_162, plain, (![C_91, D_93]: (r2_hidden(C_91, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(k4_tarski(D_93, C_91), '#skF_8'))), inference(resolution, [status(thm)], [c_118, c_159])).
% 3.16/1.54  tff(c_165, plain, (![C_91, D_93]: (r2_hidden(C_91, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden(k4_tarski(D_93, C_91), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_109, c_162])).
% 3.16/1.54  tff(c_466, plain, (![C_124]: (r2_hidden(C_124, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden(C_124, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_399, c_165])).
% 3.16/1.54  tff(c_6, plain, (![B_4, D_6, A_3, C_5]: (r2_hidden(B_4, D_6) | ~r2_hidden(k4_tarski(A_3, B_4), k2_zfmisc_1(C_5, D_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.54  tff(c_443, plain, (![C_120, D_6, C_5]: (r2_hidden(C_120, D_6) | ~r2_hidden(C_120, k2_relat_1(k2_zfmisc_1(C_5, D_6))))), inference(resolution, [status(thm)], [c_399, c_6])).
% 3.16/1.54  tff(c_480, plain, (![C_125]: (r2_hidden(C_125, '#skF_7') | ~r2_hidden(C_125, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_466, c_443])).
% 3.16/1.54  tff(c_492, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_8')), '#skF_7') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_480])).
% 3.16/1.54  tff(c_497, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_77, c_492])).
% 3.16/1.54  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.54  tff(c_500, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_8')), '#skF_7')), inference(resolution, [status(thm)], [c_497, c_10])).
% 3.16/1.54  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_500])).
% 3.16/1.54  tff(c_505, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 3.16/1.54  tff(c_554, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.54  tff(c_561, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_554])).
% 3.16/1.54  tff(c_564, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_505, c_561])).
% 3.16/1.54  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_564])).
% 3.16/1.54  tff(c_569, plain, (![A_143]: (~r2_hidden(A_143, '#skF_8'))), inference(splitRight, [status(thm)], [c_108])).
% 3.16/1.54  tff(c_579, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_2, c_569])).
% 3.16/1.54  tff(c_582, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_77])).
% 3.16/1.54  tff(c_585, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_2])).
% 3.16/1.54  tff(c_804, plain, (![A_182, C_183]: (r2_hidden(k4_tarski('#skF_5'(A_182, k2_relat_1(A_182), C_183), C_183), A_182) | ~r2_hidden(C_183, k2_relat_1(A_182)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.54  tff(c_567, plain, (![A_75]: (~r2_hidden(A_75, '#skF_8'))), inference(splitRight, [status(thm)], [c_108])).
% 3.16/1.54  tff(c_860, plain, (![C_188]: (~r2_hidden(C_188, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_804, c_567])).
% 3.16/1.54  tff(c_868, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_585, c_860])).
% 3.16/1.54  tff(c_877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_868])).
% 3.16/1.54  tff(c_878, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 3.16/1.54  tff(c_1045, plain, (![A_226, B_227, C_228]: (k1_relset_1(A_226, B_227, C_228)=k1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.54  tff(c_1052, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_1045])).
% 3.16/1.54  tff(c_1055, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_878, c_1052])).
% 3.16/1.54  tff(c_1057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1055])).
% 3.16/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  Inference rules
% 3.16/1.54  ----------------------
% 3.16/1.54  #Ref     : 0
% 3.16/1.54  #Sup     : 203
% 3.16/1.54  #Fact    : 0
% 3.16/1.54  #Define  : 0
% 3.16/1.54  #Split   : 17
% 3.16/1.54  #Chain   : 0
% 3.16/1.54  #Close   : 0
% 3.16/1.54  
% 3.16/1.54  Ordering : KBO
% 3.16/1.54  
% 3.16/1.54  Simplification rules
% 3.16/1.54  ----------------------
% 3.16/1.54  #Subsume      : 28
% 3.16/1.54  #Demod        : 40
% 3.16/1.54  #Tautology    : 47
% 3.16/1.54  #SimpNegUnit  : 18
% 3.16/1.54  #BackRed      : 18
% 3.16/1.54  
% 3.16/1.54  #Partial instantiations: 0
% 3.16/1.54  #Strategies tried      : 1
% 3.16/1.54  
% 3.16/1.54  Timing (in seconds)
% 3.16/1.54  ----------------------
% 3.21/1.54  Preprocessing        : 0.34
% 3.21/1.54  Parsing              : 0.18
% 3.21/1.54  CNF conversion       : 0.02
% 3.21/1.54  Main loop            : 0.37
% 3.21/1.54  Inferencing          : 0.14
% 3.21/1.54  Reduction            : 0.10
% 3.21/1.54  Demodulation         : 0.06
% 3.21/1.54  BG Simplification    : 0.02
% 3.21/1.54  Subsumption          : 0.07
% 3.21/1.54  Abstraction          : 0.02
% 3.21/1.54  MUC search           : 0.00
% 3.21/1.54  Cooper               : 0.00
% 3.21/1.54  Total                : 0.74
% 3.21/1.54  Index Insertion      : 0.00
% 3.21/1.54  Index Deletion       : 0.00
% 3.21/1.54  Index Matching       : 0.00
% 3.21/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
