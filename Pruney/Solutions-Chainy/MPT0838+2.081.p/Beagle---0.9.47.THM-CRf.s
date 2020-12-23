%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:20 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 135 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 239 expanded)
%              Number of equality atoms :   26 (  71 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_40,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
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

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_284,plain,(
    ! [A_108,B_109] :
      ( r2_hidden(k4_tarski('#skF_1'(A_108,B_109),'#skF_2'(A_108,B_109)),A_108)
      | r2_hidden('#skF_3'(A_108,B_109),B_109)
      | k1_relat_1(A_108) = B_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [C_80,A_81] :
      ( r2_hidden(k4_tarski(C_80,'#skF_4'(A_81,k1_relat_1(A_81),C_80)),A_81)
      | ~ r2_hidden(C_80,k1_relat_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_135,plain,(
    ! [C_80] :
      ( r2_hidden(k4_tarski(C_80,'#skF_4'(k1_xboole_0,k1_xboole_0,C_80)),k1_xboole_0)
      | ~ r2_hidden(C_80,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_151,plain,(
    ! [C_83] :
      ( r2_hidden(k4_tarski(C_83,'#skF_4'(k1_xboole_0,k1_xboole_0,C_83)),k1_xboole_0)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_135])).

tff(c_30,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,(
    ! [C_83] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_83,'#skF_4'(k1_xboole_0,k1_xboole_0,C_83)))
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_151,c_30])).

tff(c_162,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_299,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_109),B_109)
      | k1_relat_1(k1_xboole_0) = B_109 ) ),
    inference(resolution,[status(thm)],[c_284,c_162])).

tff(c_334,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_111),B_111)
      | k1_xboole_0 = B_111 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_299])).

tff(c_117,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_121,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_38,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_relset_1('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_140,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_relat_1('#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_38])).

tff(c_357,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_334,c_140])).

tff(c_371,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_357])).

tff(c_173,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k2_relset_1(A_86,B_87,C_88),k1_zfmisc_1(B_87))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_189,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_173])).

tff(c_195,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_189])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( m1_subset_1(A_2,C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(C_4))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_2] :
      ( m1_subset_1(A_2,'#skF_6')
      | ~ r2_hidden(A_2,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_195,c_4])).

tff(c_349,plain,
    ( m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_334,c_201])).

tff(c_366,plain,(
    m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_349])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_366])).

tff(c_391,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_418,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_421,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_418])).

tff(c_423,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_421])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.25/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.25/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.25/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.67/1.34  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.67/1.34  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.67/1.34  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.67/1.34  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.67/1.34  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.67/1.34  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.67/1.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.34  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.67/1.34  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.67/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.67/1.34  tff(f_33, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.67/1.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.67/1.34  tff(c_40, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.67/1.34  tff(c_20, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.67/1.34  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.67/1.34  tff(c_64, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.34  tff(c_67, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.67/1.34  tff(c_70, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 2.67/1.34  tff(c_26, plain, (![A_29]: (k1_relat_1(A_29)=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.34  tff(c_74, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_26])).
% 2.67/1.34  tff(c_75, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 2.67/1.34  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.34  tff(c_284, plain, (![A_108, B_109]: (r2_hidden(k4_tarski('#skF_1'(A_108, B_109), '#skF_2'(A_108, B_109)), A_108) | r2_hidden('#skF_3'(A_108, B_109), B_109) | k1_relat_1(A_108)=B_109)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.34  tff(c_122, plain, (![C_80, A_81]: (r2_hidden(k4_tarski(C_80, '#skF_4'(A_81, k1_relat_1(A_81), C_80)), A_81) | ~r2_hidden(C_80, k1_relat_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.34  tff(c_135, plain, (![C_80]: (r2_hidden(k4_tarski(C_80, '#skF_4'(k1_xboole_0, k1_xboole_0, C_80)), k1_xboole_0) | ~r2_hidden(C_80, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_122])).
% 2.67/1.34  tff(c_151, plain, (![C_83]: (r2_hidden(k4_tarski(C_83, '#skF_4'(k1_xboole_0, k1_xboole_0, C_83)), k1_xboole_0) | ~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_135])).
% 2.67/1.34  tff(c_30, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.34  tff(c_157, plain, (![C_83]: (~r1_tarski(k1_xboole_0, k4_tarski(C_83, '#skF_4'(k1_xboole_0, k1_xboole_0, C_83))) | ~r2_hidden(C_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_151, c_30])).
% 2.67/1.34  tff(c_162, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_157])).
% 2.67/1.34  tff(c_299, plain, (![B_109]: (r2_hidden('#skF_3'(k1_xboole_0, B_109), B_109) | k1_relat_1(k1_xboole_0)=B_109)), inference(resolution, [status(thm)], [c_284, c_162])).
% 2.67/1.34  tff(c_334, plain, (![B_111]: (r2_hidden('#skF_3'(k1_xboole_0, B_111), B_111) | k1_xboole_0=B_111)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_299])).
% 2.67/1.34  tff(c_117, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.34  tff(c_121, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_117])).
% 2.67/1.34  tff(c_38, plain, (![D_52]: (~r2_hidden(D_52, k2_relset_1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.67/1.34  tff(c_140, plain, (![D_52]: (~r2_hidden(D_52, k2_relat_1('#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_38])).
% 2.67/1.34  tff(c_357, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_334, c_140])).
% 2.67/1.34  tff(c_371, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_75, c_357])).
% 2.67/1.34  tff(c_173, plain, (![A_86, B_87, C_88]: (m1_subset_1(k2_relset_1(A_86, B_87, C_88), k1_zfmisc_1(B_87)) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.34  tff(c_189, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_121, c_173])).
% 2.67/1.34  tff(c_195, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_189])).
% 2.67/1.34  tff(c_4, plain, (![A_2, C_4, B_3]: (m1_subset_1(A_2, C_4) | ~m1_subset_1(B_3, k1_zfmisc_1(C_4)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.34  tff(c_201, plain, (![A_2]: (m1_subset_1(A_2, '#skF_6') | ~r2_hidden(A_2, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_195, c_4])).
% 2.67/1.34  tff(c_349, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_334, c_201])).
% 2.67/1.34  tff(c_366, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_75, c_349])).
% 2.67/1.34  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_366])).
% 2.67/1.34  tff(c_391, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 2.67/1.34  tff(c_418, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.34  tff(c_421, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_418])).
% 2.67/1.34  tff(c_423, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_391, c_421])).
% 2.67/1.34  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_423])).
% 2.67/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  Inference rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Ref     : 0
% 2.67/1.34  #Sup     : 78
% 2.67/1.34  #Fact    : 0
% 2.67/1.34  #Define  : 0
% 2.67/1.34  #Split   : 2
% 2.67/1.34  #Chain   : 0
% 2.67/1.34  #Close   : 0
% 2.67/1.34  
% 2.67/1.34  Ordering : KBO
% 2.67/1.34  
% 2.67/1.34  Simplification rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Subsume      : 17
% 2.67/1.34  #Demod        : 27
% 2.67/1.34  #Tautology    : 22
% 2.67/1.34  #SimpNegUnit  : 6
% 2.67/1.34  #BackRed      : 4
% 2.67/1.34  
% 2.67/1.34  #Partial instantiations: 0
% 2.67/1.34  #Strategies tried      : 1
% 2.67/1.34  
% 2.67/1.34  Timing (in seconds)
% 2.67/1.34  ----------------------
% 2.67/1.34  Preprocessing        : 0.33
% 2.67/1.34  Parsing              : 0.18
% 2.67/1.34  CNF conversion       : 0.02
% 2.67/1.34  Main loop            : 0.25
% 2.67/1.34  Inferencing          : 0.09
% 2.67/1.34  Reduction            : 0.07
% 2.67/1.34  Demodulation         : 0.05
% 2.67/1.34  BG Simplification    : 0.01
% 2.67/1.34  Subsumption          : 0.05
% 2.67/1.34  Abstraction          : 0.02
% 2.67/1.34  MUC search           : 0.00
% 2.67/1.34  Cooper               : 0.00
% 2.67/1.34  Total                : 0.61
% 2.67/1.34  Index Insertion      : 0.00
% 2.67/1.34  Index Deletion       : 0.00
% 2.67/1.34  Index Matching       : 0.00
% 2.67/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
