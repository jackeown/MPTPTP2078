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
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 159 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 286 expanded)
%              Number of equality atoms :   32 (  75 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_50,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_90,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_100,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_96])).

tff(c_34,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) = k1_xboole_0
      | k1_relat_1(A_33) != k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_34])).

tff(c_109,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_133,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_142,plain,(
    v4_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_200,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,A_95) = B_94
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_206,plain,
    ( k7_relat_1('#skF_7','#skF_6') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_142,c_200])).

tff(c_212,plain,(
    k7_relat_1('#skF_7','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_206])).

tff(c_36,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_35,A_34)),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_216,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_36])).

tff(c_220,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_216])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_570,plain,(
    ! [A_159,B_160] :
      ( r2_hidden(k4_tarski('#skF_2'(A_159,B_160),'#skF_1'(A_159,B_160)),A_159)
      | r2_hidden('#skF_3'(A_159,B_160),B_160)
      | k2_relat_1(A_159) = B_160 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_347,plain,(
    ! [A_126,C_127] :
      ( r2_hidden(k4_tarski('#skF_4'(A_126,k2_relat_1(A_126),C_127),C_127),A_126)
      | ~ r2_hidden(C_127,k2_relat_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_365,plain,(
    ! [C_127] :
      ( r2_hidden(k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_127),C_127),k1_xboole_0)
      | ~ r2_hidden(C_127,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_347])).

tff(c_403,plain,(
    ! [C_136] :
      ( r2_hidden(k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_136),C_136),k1_xboole_0)
      | ~ r2_hidden(C_136,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_365])).

tff(c_38,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_411,plain,(
    ! [C_136] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_136),C_136))
      | ~ r2_hidden(C_136,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_403,c_38])).

tff(c_419,plain,(
    ! [C_136] : ~ r2_hidden(C_136,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_411])).

tff(c_594,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_160),B_160)
      | k2_relat_1(k1_xboole_0) = B_160 ) ),
    inference(resolution,[status(thm)],[c_570,c_419])).

tff(c_618,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_161),B_161)
      | k1_xboole_0 = B_161 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_594])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [A_99,C_100,B_101] :
      ( m1_subset_1(A_99,C_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(C_100))
      | ~ r2_hidden(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [A_99,B_3,A_2] :
      ( m1_subset_1(A_99,B_3)
      | ~ r2_hidden(A_99,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_707,plain,(
    ! [B_167,B_168] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_167),B_168)
      | ~ r1_tarski(B_167,B_168)
      | k1_xboole_0 = B_167 ) ),
    inference(resolution,[status(thm)],[c_618,c_263])).

tff(c_267,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_276,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_267])).

tff(c_48,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_277,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_58,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_48])).

tff(c_646,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_618,c_277])).

tff(c_661,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_646])).

tff(c_710,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_707,c_661])).

tff(c_740,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_710])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_740])).

tff(c_743,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_905,plain,(
    ! [A_197,B_198,C_199] :
      ( k2_relset_1(A_197,B_198,C_199) = k2_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_912,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_905])).

tff(c_915,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_912])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:08:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.86/1.42  
% 2.86/1.42  %Foreground sorts:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Background operators:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Foreground operators:
% 2.86/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.86/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.86/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.42  
% 2.86/1.44  tff(f_113, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.86/1.44  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.86/1.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.86/1.44  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.86/1.44  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.44  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.86/1.44  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.86/1.44  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.86/1.44  tff(f_52, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.86/1.44  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.44  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.86/1.44  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.44  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.86/1.44  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.86/1.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.86/1.44  tff(c_50, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.44  tff(c_24, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.44  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.44  tff(c_90, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.44  tff(c_96, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_90])).
% 2.86/1.44  tff(c_100, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_96])).
% 2.86/1.44  tff(c_34, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | k1_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_107, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_34])).
% 2.86/1.44  tff(c_109, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_107])).
% 2.86/1.44  tff(c_133, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.86/1.44  tff(c_142, plain, (v4_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_133])).
% 2.86/1.44  tff(c_200, plain, (![B_94, A_95]: (k7_relat_1(B_94, A_95)=B_94 | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.44  tff(c_206, plain, (k7_relat_1('#skF_7', '#skF_6')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_142, c_200])).
% 2.86/1.44  tff(c_212, plain, (k7_relat_1('#skF_7', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_206])).
% 2.86/1.44  tff(c_36, plain, (![B_35, A_34]: (r1_tarski(k1_relat_1(k7_relat_1(B_35, A_34)), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.86/1.44  tff(c_216, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_212, c_36])).
% 2.86/1.44  tff(c_220, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_216])).
% 2.86/1.44  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.86/1.44  tff(c_570, plain, (![A_159, B_160]: (r2_hidden(k4_tarski('#skF_2'(A_159, B_160), '#skF_1'(A_159, B_160)), A_159) | r2_hidden('#skF_3'(A_159, B_160), B_160) | k2_relat_1(A_159)=B_160)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.44  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.44  tff(c_347, plain, (![A_126, C_127]: (r2_hidden(k4_tarski('#skF_4'(A_126, k2_relat_1(A_126), C_127), C_127), A_126) | ~r2_hidden(C_127, k2_relat_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.44  tff(c_365, plain, (![C_127]: (r2_hidden(k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_127), C_127), k1_xboole_0) | ~r2_hidden(C_127, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_347])).
% 2.86/1.44  tff(c_403, plain, (![C_136]: (r2_hidden(k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_136), C_136), k1_xboole_0) | ~r2_hidden(C_136, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_365])).
% 2.86/1.44  tff(c_38, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.44  tff(c_411, plain, (![C_136]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_136), C_136)) | ~r2_hidden(C_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_403, c_38])).
% 2.86/1.44  tff(c_419, plain, (![C_136]: (~r2_hidden(C_136, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_411])).
% 2.86/1.44  tff(c_594, plain, (![B_160]: (r2_hidden('#skF_3'(k1_xboole_0, B_160), B_160) | k2_relat_1(k1_xboole_0)=B_160)), inference(resolution, [status(thm)], [c_570, c_419])).
% 2.86/1.44  tff(c_618, plain, (![B_161]: (r2_hidden('#skF_3'(k1_xboole_0, B_161), B_161) | k1_xboole_0=B_161)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_594])).
% 2.86/1.44  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.44  tff(c_258, plain, (![A_99, C_100, B_101]: (m1_subset_1(A_99, C_100) | ~m1_subset_1(B_101, k1_zfmisc_1(C_100)) | ~r2_hidden(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.44  tff(c_263, plain, (![A_99, B_3, A_2]: (m1_subset_1(A_99, B_3) | ~r2_hidden(A_99, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_258])).
% 2.86/1.44  tff(c_707, plain, (![B_167, B_168]: (m1_subset_1('#skF_3'(k1_xboole_0, B_167), B_168) | ~r1_tarski(B_167, B_168) | k1_xboole_0=B_167)), inference(resolution, [status(thm)], [c_618, c_263])).
% 2.86/1.44  tff(c_267, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.44  tff(c_276, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_267])).
% 2.86/1.44  tff(c_48, plain, (![D_58]: (~r2_hidden(D_58, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.44  tff(c_277, plain, (![D_58]: (~r2_hidden(D_58, k1_relat_1('#skF_7')) | ~m1_subset_1(D_58, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_48])).
% 2.86/1.44  tff(c_646, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_618, c_277])).
% 2.86/1.44  tff(c_661, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_109, c_646])).
% 2.86/1.44  tff(c_710, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_707, c_661])).
% 2.86/1.44  tff(c_740, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_220, c_710])).
% 2.86/1.44  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_740])).
% 2.86/1.44  tff(c_743, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_107])).
% 2.86/1.44  tff(c_905, plain, (![A_197, B_198, C_199]: (k2_relset_1(A_197, B_198, C_199)=k2_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.44  tff(c_912, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_905])).
% 2.86/1.44  tff(c_915, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_743, c_912])).
% 2.86/1.44  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_915])).
% 2.86/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  Inference rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Ref     : 0
% 2.86/1.44  #Sup     : 172
% 2.86/1.44  #Fact    : 0
% 2.86/1.44  #Define  : 0
% 2.86/1.44  #Split   : 5
% 2.86/1.44  #Chain   : 0
% 2.86/1.44  #Close   : 0
% 2.86/1.44  
% 2.86/1.44  Ordering : KBO
% 2.86/1.44  
% 2.86/1.44  Simplification rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Subsume      : 33
% 2.86/1.44  #Demod        : 102
% 2.86/1.44  #Tautology    : 59
% 2.86/1.44  #SimpNegUnit  : 12
% 2.86/1.44  #BackRed      : 11
% 2.86/1.44  
% 2.86/1.44  #Partial instantiations: 0
% 2.86/1.44  #Strategies tried      : 1
% 2.86/1.44  
% 2.86/1.44  Timing (in seconds)
% 2.86/1.44  ----------------------
% 2.86/1.44  Preprocessing        : 0.32
% 2.86/1.44  Parsing              : 0.16
% 2.86/1.44  CNF conversion       : 0.02
% 2.86/1.44  Main loop            : 0.35
% 2.86/1.44  Inferencing          : 0.13
% 2.86/1.44  Reduction            : 0.11
% 2.86/1.44  Demodulation         : 0.07
% 2.86/1.44  BG Simplification    : 0.02
% 2.86/1.44  Subsumption          : 0.06
% 2.86/1.44  Abstraction          : 0.02
% 2.86/1.44  MUC search           : 0.00
% 2.86/1.44  Cooper               : 0.00
% 2.86/1.44  Total                : 0.71
% 2.86/1.44  Index Insertion      : 0.00
% 2.86/1.44  Index Deletion       : 0.00
% 2.86/1.44  Index Matching       : 0.00
% 2.86/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
