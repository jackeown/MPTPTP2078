%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 159 expanded)
%              Number of leaves         :   35 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 293 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67])).

tff(c_26,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) = k1_xboole_0
      | k2_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_26])).

tff(c_75,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_76,plain,(
    ! [A_62] :
      ( k2_relat_1(A_62) = k1_xboole_0
      | k1_relat_1(A_62) != k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_85,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_79])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_279,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(k4_tarski('#skF_1'(A_109,B_110),'#skF_2'(A_109,B_110)),A_109)
      | r2_hidden('#skF_3'(A_109,B_110),B_110)
      | k1_relat_1(A_109) = B_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [C_88,A_89] :
      ( r2_hidden(k4_tarski(C_88,'#skF_4'(A_89,k1_relat_1(A_89),C_88)),A_89)
      | ~ r2_hidden(C_88,k1_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    ! [C_88] :
      ( r2_hidden(k4_tarski(C_88,'#skF_4'(k1_xboole_0,k1_xboole_0,C_88)),k1_xboole_0)
      | ~ r2_hidden(C_88,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_176])).

tff(c_200,plain,(
    ! [C_93] :
      ( r2_hidden(k4_tarski(C_93,'#skF_4'(k1_xboole_0,k1_xboole_0,C_93)),k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_193])).

tff(c_30,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_206,plain,(
    ! [C_93] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_93,'#skF_4'(k1_xboole_0,k1_xboole_0,C_93)))
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_200,c_30])).

tff(c_211,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_290,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_110),B_110)
      | k1_relat_1(k1_xboole_0) = B_110 ) ),
    inference(resolution,[status(thm)],[c_279,c_211])).

tff(c_329,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_112),B_112)
      | k1_xboole_0 = B_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_290])).

tff(c_107,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_107])).

tff(c_38,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_112,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_38])).

tff(c_352,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_329,c_112])).

tff(c_366,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_352])).

tff(c_138,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1(k1_relset_1(A_83,B_84,C_85),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_138])).

tff(c_160,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_154])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    ! [A_2] :
      ( m1_subset_1(A_2,'#skF_6')
      | ~ r2_hidden(A_2,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_348,plain,
    ( m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_329,c_167])).

tff(c_363,plain,(
    m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_348])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_363])).

tff(c_388,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_440,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_443,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_440])).

tff(c_445,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_443])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.59  
% 2.77/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.59  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.77/1.59  
% 2.77/1.59  %Foreground sorts:
% 2.77/1.59  
% 2.77/1.59  
% 2.77/1.59  %Background operators:
% 2.77/1.59  
% 2.77/1.59  
% 2.77/1.59  %Foreground operators:
% 2.77/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.77/1.59  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.59  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.59  
% 3.08/1.61  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.08/1.61  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.61  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.61  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.08/1.61  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.08/1.61  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.08/1.61  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.61  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.08/1.61  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.61  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.08/1.61  tff(f_33, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.08/1.61  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.61  tff(c_40, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.61  tff(c_20, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.08/1.61  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.61  tff(c_64, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.61  tff(c_67, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_64])).
% 3.08/1.61  tff(c_70, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 3.08/1.61  tff(c_26, plain, (![A_29]: (k1_relat_1(A_29)=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.61  tff(c_74, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_26])).
% 3.08/1.61  tff(c_75, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 3.08/1.61  tff(c_76, plain, (![A_62]: (k2_relat_1(A_62)=k1_xboole_0 | k1_relat_1(A_62)!=k1_xboole_0 | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.08/1.61  tff(c_79, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_76])).
% 3.08/1.61  tff(c_85, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_75, c_79])).
% 3.08/1.61  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.08/1.61  tff(c_279, plain, (![A_109, B_110]: (r2_hidden(k4_tarski('#skF_1'(A_109, B_110), '#skF_2'(A_109, B_110)), A_109) | r2_hidden('#skF_3'(A_109, B_110), B_110) | k1_relat_1(A_109)=B_110)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.61  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.61  tff(c_176, plain, (![C_88, A_89]: (r2_hidden(k4_tarski(C_88, '#skF_4'(A_89, k1_relat_1(A_89), C_88)), A_89) | ~r2_hidden(C_88, k1_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.61  tff(c_193, plain, (![C_88]: (r2_hidden(k4_tarski(C_88, '#skF_4'(k1_xboole_0, k1_xboole_0, C_88)), k1_xboole_0) | ~r2_hidden(C_88, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_176])).
% 3.08/1.61  tff(c_200, plain, (![C_93]: (r2_hidden(k4_tarski(C_93, '#skF_4'(k1_xboole_0, k1_xboole_0, C_93)), k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_193])).
% 3.08/1.61  tff(c_30, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.61  tff(c_206, plain, (![C_93]: (~r1_tarski(k1_xboole_0, k4_tarski(C_93, '#skF_4'(k1_xboole_0, k1_xboole_0, C_93))) | ~r2_hidden(C_93, k1_xboole_0))), inference(resolution, [status(thm)], [c_200, c_30])).
% 3.08/1.61  tff(c_211, plain, (![C_93]: (~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_206])).
% 3.08/1.61  tff(c_290, plain, (![B_110]: (r2_hidden('#skF_3'(k1_xboole_0, B_110), B_110) | k1_relat_1(k1_xboole_0)=B_110)), inference(resolution, [status(thm)], [c_279, c_211])).
% 3.08/1.61  tff(c_329, plain, (![B_112]: (r2_hidden('#skF_3'(k1_xboole_0, B_112), B_112) | k1_xboole_0=B_112)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_290])).
% 3.08/1.61  tff(c_107, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.08/1.61  tff(c_111, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_107])).
% 3.08/1.61  tff(c_38, plain, (![D_52]: (~r2_hidden(D_52, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.61  tff(c_112, plain, (![D_52]: (~r2_hidden(D_52, k1_relat_1('#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_38])).
% 3.08/1.61  tff(c_352, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_329, c_112])).
% 3.08/1.61  tff(c_366, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_352])).
% 3.08/1.61  tff(c_138, plain, (![A_83, B_84, C_85]: (m1_subset_1(k1_relset_1(A_83, B_84, C_85), k1_zfmisc_1(A_83)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.61  tff(c_154, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_138])).
% 3.08/1.61  tff(c_160, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_154])).
% 3.08/1.61  tff(c_4, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.61  tff(c_167, plain, (![A_2]: (m1_subset_1(A_2, '#skF_6') | ~r2_hidden(A_2, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_160, c_4])).
% 3.08/1.61  tff(c_348, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_329, c_167])).
% 3.08/1.61  tff(c_363, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_348])).
% 3.08/1.61  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_366, c_363])).
% 3.08/1.61  tff(c_388, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 3.08/1.61  tff(c_440, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.61  tff(c_443, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_440])).
% 3.08/1.61  tff(c_445, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_388, c_443])).
% 3.08/1.61  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_445])).
% 3.08/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.61  
% 3.08/1.61  Inference rules
% 3.08/1.61  ----------------------
% 3.08/1.61  #Ref     : 0
% 3.08/1.61  #Sup     : 83
% 3.08/1.61  #Fact    : 0
% 3.08/1.61  #Define  : 0
% 3.08/1.61  #Split   : 2
% 3.08/1.61  #Chain   : 0
% 3.08/1.61  #Close   : 0
% 3.08/1.61  
% 3.08/1.61  Ordering : KBO
% 3.08/1.61  
% 3.08/1.61  Simplification rules
% 3.08/1.61  ----------------------
% 3.08/1.61  #Subsume      : 16
% 3.08/1.61  #Demod        : 27
% 3.08/1.61  #Tautology    : 27
% 3.08/1.61  #SimpNegUnit  : 6
% 3.08/1.61  #BackRed      : 5
% 3.08/1.61  
% 3.08/1.61  #Partial instantiations: 0
% 3.08/1.61  #Strategies tried      : 1
% 3.08/1.61  
% 3.08/1.61  Timing (in seconds)
% 3.08/1.61  ----------------------
% 3.08/1.61  Preprocessing        : 0.40
% 3.08/1.61  Parsing              : 0.22
% 3.08/1.61  CNF conversion       : 0.03
% 3.08/1.61  Main loop            : 0.37
% 3.08/1.61  Inferencing          : 0.14
% 3.08/1.62  Reduction            : 0.10
% 3.08/1.62  Demodulation         : 0.07
% 3.08/1.62  BG Simplification    : 0.02
% 3.08/1.62  Subsumption          : 0.07
% 3.08/1.62  Abstraction          : 0.02
% 3.08/1.62  MUC search           : 0.00
% 3.08/1.62  Cooper               : 0.00
% 3.08/1.62  Total                : 0.81
% 3.08/1.62  Index Insertion      : 0.00
% 3.08/1.62  Index Deletion       : 0.00
% 3.08/1.62  Index Matching       : 0.00
% 3.08/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
