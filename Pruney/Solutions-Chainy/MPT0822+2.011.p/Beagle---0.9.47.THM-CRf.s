%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 245 expanded)
%              Number of leaves         :   24 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :   99 ( 502 expanded)
%              Number of equality atoms :   30 ( 164 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

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

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_26,plain,
    ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_41,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_33])).

tff(c_55,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k2_relset_1(A_52,B_53,C_54),k1_zfmisc_1(B_53))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_55])).

tff(c_65,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_213,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(k4_tarski('#skF_2'(A_83,B_84),'#skF_1'(A_83,B_84)),A_83)
      | r2_hidden('#skF_3'(A_83,B_84),B_84)
      | k2_relat_1(A_83) = B_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k2_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(D_23,C_20),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_250,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),k2_relat_1(A_86))
      | r2_hidden('#skF_3'(A_86,B_87),B_87)
      | k2_relat_1(A_86) = B_87 ) ),
    inference(resolution,[status(thm)],[c_213,c_6])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1186,plain,(
    ! [A_158,B_159,A_160] :
      ( r2_hidden('#skF_1'(A_158,B_159),A_160)
      | ~ m1_subset_1(k2_relat_1(A_158),k1_zfmisc_1(A_160))
      | r2_hidden('#skF_3'(A_158,B_159),B_159)
      | k2_relat_1(A_158) = B_159 ) ),
    inference(resolution,[status(thm)],[c_250,c_2])).

tff(c_1189,plain,(
    ! [B_159] :
      ( r2_hidden('#skF_1'('#skF_7',B_159),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_159),B_159)
      | k2_relat_1('#skF_7') = B_159 ) ),
    inference(resolution,[status(thm)],[c_65,c_1186])).

tff(c_32,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_8'(D_36),D_36),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6')
      | k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_8'(D_36),D_36),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_75,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_8'(D_36),D_36),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_74])).

tff(c_289,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden(k4_tarski('#skF_2'(A_97,B_98),'#skF_1'(A_97,B_98)),A_97)
      | ~ r2_hidden(k4_tarski(D_99,'#skF_3'(A_97,B_98)),A_97)
      | k2_relat_1(A_97) = B_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_385,plain,(
    ! [B_105] :
      ( r2_hidden(k4_tarski('#skF_2'('#skF_7',B_105),'#skF_1'('#skF_7',B_105)),'#skF_7')
      | k2_relat_1('#skF_7') = B_105
      | ~ r2_hidden('#skF_3'('#skF_7',B_105),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_75,c_289])).

tff(c_393,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_1'('#skF_7',B_106),k2_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_106
      | ~ r2_hidden('#skF_3'('#skF_7',B_106),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_385,c_6])).

tff(c_2669,plain,(
    ! [B_239,A_240] :
      ( r2_hidden('#skF_1'('#skF_7',B_239),A_240)
      | ~ m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1(A_240))
      | k2_relat_1('#skF_7') = B_239
      | ~ r2_hidden('#skF_3'('#skF_7',B_239),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_2673,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_1'('#skF_7',B_241),'#skF_6')
      | k2_relat_1('#skF_7') = B_241
      | ~ r2_hidden('#skF_3'('#skF_7',B_241),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_65,c_2669])).

tff(c_2685,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1189,c_2673])).

tff(c_2695,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_41,c_2685])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_3'(A_5,B_6),B_6)
      | k2_relat_1(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_5,B_6,D_19] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | ~ r2_hidden(k4_tarski(D_19,'#skF_3'(A_5,B_6)),A_5)
      | k2_relat_1(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2703,plain,(
    ! [D_19] :
      ( ~ r2_hidden(k4_tarski(D_19,'#skF_3'('#skF_7','#skF_6')),'#skF_7')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2695,c_8])).

tff(c_2713,plain,(
    ! [D_242] : ~ r2_hidden(k4_tarski(D_242,'#skF_3'('#skF_7','#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_2703])).

tff(c_2737,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_75,c_2713])).

tff(c_2750,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_2737])).

tff(c_2759,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_2750])).

tff(c_2761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_2759])).

tff(c_2762,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2763,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2778,plain,(
    ! [A_251,B_252,C_253] :
      ( k2_relset_1(A_251,B_252,C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2781,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_2778])).

tff(c_2783,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_2781])).

tff(c_2808,plain,(
    ! [A_259,C_260] :
      ( r2_hidden(k4_tarski('#skF_4'(A_259,k2_relat_1(A_259),C_260),C_260),A_259)
      | ~ r2_hidden(C_260,k2_relat_1(A_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [E_39] :
      ( k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski(E_39,'#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2775,plain,(
    ! [E_39] : ~ r2_hidden(k4_tarski(E_39,'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_22])).

tff(c_2812,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2808,c_2775])).

tff(c_2824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2783,c_2812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.09  
% 5.33/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.10  %$ r2_hidden > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 5.33/2.10  
% 5.33/2.10  %Foreground sorts:
% 5.33/2.10  
% 5.33/2.10  
% 5.33/2.10  %Background operators:
% 5.33/2.10  
% 5.33/2.10  
% 5.33/2.10  %Foreground operators:
% 5.33/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.33/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.33/2.10  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.33/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.33/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.33/2.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.33/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.33/2.10  tff('#skF_9', type, '#skF_9': $i).
% 5.33/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.33/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.33/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.10  
% 5.33/2.11  tff(f_61, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 5.33/2.11  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.33/2.11  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.33/2.11  tff(f_40, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.33/2.11  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.33/2.11  tff(c_20, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.33/2.11  tff(c_36, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.33/2.11  tff(c_40, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_36])).
% 5.33/2.11  tff(c_26, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.33/2.11  tff(c_33, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_26])).
% 5.33/2.11  tff(c_41, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_33])).
% 5.33/2.11  tff(c_55, plain, (![A_52, B_53, C_54]: (m1_subset_1(k2_relset_1(A_52, B_53, C_54), k1_zfmisc_1(B_53)) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.33/2.11  tff(c_62, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_55])).
% 5.33/2.11  tff(c_65, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 5.33/2.11  tff(c_213, plain, (![A_83, B_84]: (r2_hidden(k4_tarski('#skF_2'(A_83, B_84), '#skF_1'(A_83, B_84)), A_83) | r2_hidden('#skF_3'(A_83, B_84), B_84) | k2_relat_1(A_83)=B_84)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_6, plain, (![C_20, A_5, D_23]: (r2_hidden(C_20, k2_relat_1(A_5)) | ~r2_hidden(k4_tarski(D_23, C_20), A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_250, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), k2_relat_1(A_86)) | r2_hidden('#skF_3'(A_86, B_87), B_87) | k2_relat_1(A_86)=B_87)), inference(resolution, [status(thm)], [c_213, c_6])).
% 5.33/2.11  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/2.11  tff(c_1186, plain, (![A_158, B_159, A_160]: (r2_hidden('#skF_1'(A_158, B_159), A_160) | ~m1_subset_1(k2_relat_1(A_158), k1_zfmisc_1(A_160)) | r2_hidden('#skF_3'(A_158, B_159), B_159) | k2_relat_1(A_158)=B_159)), inference(resolution, [status(thm)], [c_250, c_2])).
% 5.33/2.11  tff(c_1189, plain, (![B_159]: (r2_hidden('#skF_1'('#skF_7', B_159), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_159), B_159) | k2_relat_1('#skF_7')=B_159)), inference(resolution, [status(thm)], [c_65, c_1186])).
% 5.33/2.11  tff(c_32, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_8'(D_36), D_36), '#skF_7') | ~r2_hidden(D_36, '#skF_6') | k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.33/2.11  tff(c_74, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_8'(D_36), D_36), '#skF_7') | ~r2_hidden(D_36, '#skF_6') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 5.33/2.11  tff(c_75, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_8'(D_36), D_36), '#skF_7') | ~r2_hidden(D_36, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_41, c_74])).
% 5.33/2.11  tff(c_289, plain, (![A_97, B_98, D_99]: (r2_hidden(k4_tarski('#skF_2'(A_97, B_98), '#skF_1'(A_97, B_98)), A_97) | ~r2_hidden(k4_tarski(D_99, '#skF_3'(A_97, B_98)), A_97) | k2_relat_1(A_97)=B_98)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_385, plain, (![B_105]: (r2_hidden(k4_tarski('#skF_2'('#skF_7', B_105), '#skF_1'('#skF_7', B_105)), '#skF_7') | k2_relat_1('#skF_7')=B_105 | ~r2_hidden('#skF_3'('#skF_7', B_105), '#skF_6'))), inference(resolution, [status(thm)], [c_75, c_289])).
% 5.33/2.11  tff(c_393, plain, (![B_106]: (r2_hidden('#skF_1'('#skF_7', B_106), k2_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_106 | ~r2_hidden('#skF_3'('#skF_7', B_106), '#skF_6'))), inference(resolution, [status(thm)], [c_385, c_6])).
% 5.33/2.11  tff(c_2669, plain, (![B_239, A_240]: (r2_hidden('#skF_1'('#skF_7', B_239), A_240) | ~m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1(A_240)) | k2_relat_1('#skF_7')=B_239 | ~r2_hidden('#skF_3'('#skF_7', B_239), '#skF_6'))), inference(resolution, [status(thm)], [c_393, c_2])).
% 5.33/2.11  tff(c_2673, plain, (![B_241]: (r2_hidden('#skF_1'('#skF_7', B_241), '#skF_6') | k2_relat_1('#skF_7')=B_241 | ~r2_hidden('#skF_3'('#skF_7', B_241), '#skF_6'))), inference(resolution, [status(thm)], [c_65, c_2669])).
% 5.33/2.11  tff(c_2685, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1189, c_2673])).
% 5.33/2.11  tff(c_2695, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_41, c_41, c_2685])).
% 5.33/2.11  tff(c_12, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r2_hidden('#skF_3'(A_5, B_6), B_6) | k2_relat_1(A_5)=B_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_8, plain, (![A_5, B_6, D_19]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | ~r2_hidden(k4_tarski(D_19, '#skF_3'(A_5, B_6)), A_5) | k2_relat_1(A_5)=B_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_2703, plain, (![D_19]: (~r2_hidden(k4_tarski(D_19, '#skF_3'('#skF_7', '#skF_6')), '#skF_7') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_2695, c_8])).
% 5.33/2.11  tff(c_2713, plain, (![D_242]: (~r2_hidden(k4_tarski(D_242, '#skF_3'('#skF_7', '#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_41, c_2703])).
% 5.33/2.11  tff(c_2737, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_75, c_2713])).
% 5.33/2.11  tff(c_2750, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_12, c_2737])).
% 5.33/2.11  tff(c_2759, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_2750])).
% 5.33/2.11  tff(c_2761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_2759])).
% 5.33/2.11  tff(c_2762, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 5.33/2.11  tff(c_2763, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 5.33/2.11  tff(c_2778, plain, (![A_251, B_252, C_253]: (k2_relset_1(A_251, B_252, C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.33/2.11  tff(c_2781, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_2778])).
% 5.33/2.11  tff(c_2783, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_2781])).
% 5.33/2.11  tff(c_2808, plain, (![A_259, C_260]: (r2_hidden(k4_tarski('#skF_4'(A_259, k2_relat_1(A_259), C_260), C_260), A_259) | ~r2_hidden(C_260, k2_relat_1(A_259)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.33/2.11  tff(c_22, plain, (![E_39]: (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski(E_39, '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.33/2.11  tff(c_2775, plain, (![E_39]: (~r2_hidden(k4_tarski(E_39, '#skF_9'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_22])).
% 5.33/2.11  tff(c_2812, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2808, c_2775])).
% 5.33/2.11  tff(c_2824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2783, c_2812])).
% 5.33/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.11  
% 5.33/2.11  Inference rules
% 5.33/2.11  ----------------------
% 5.33/2.11  #Ref     : 0
% 5.33/2.11  #Sup     : 651
% 5.33/2.11  #Fact    : 0
% 5.33/2.11  #Define  : 0
% 5.33/2.11  #Split   : 16
% 5.33/2.11  #Chain   : 0
% 5.33/2.11  #Close   : 0
% 5.33/2.11  
% 5.33/2.11  Ordering : KBO
% 5.33/2.11  
% 5.33/2.11  Simplification rules
% 5.33/2.11  ----------------------
% 5.33/2.11  #Subsume      : 82
% 5.33/2.11  #Demod        : 24
% 5.33/2.11  #Tautology    : 36
% 5.33/2.11  #SimpNegUnit  : 8
% 5.33/2.11  #BackRed      : 1
% 5.33/2.11  
% 5.33/2.11  #Partial instantiations: 0
% 5.33/2.11  #Strategies tried      : 1
% 5.33/2.11  
% 5.33/2.11  Timing (in seconds)
% 5.33/2.11  ----------------------
% 5.33/2.11  Preprocessing        : 0.34
% 5.33/2.11  Parsing              : 0.17
% 5.33/2.11  CNF conversion       : 0.03
% 5.33/2.11  Main loop            : 0.93
% 5.33/2.11  Inferencing          : 0.29
% 5.33/2.11  Reduction            : 0.22
% 5.33/2.11  Demodulation         : 0.14
% 5.33/2.11  BG Simplification    : 0.04
% 5.33/2.11  Subsumption          : 0.31
% 5.33/2.11  Abstraction          : 0.05
% 5.33/2.11  MUC search           : 0.00
% 5.33/2.11  Cooper               : 0.00
% 5.33/2.11  Total                : 1.30
% 5.33/2.11  Index Insertion      : 0.00
% 5.33/2.11  Index Deletion       : 0.00
% 5.33/2.11  Index Matching       : 0.00
% 5.33/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
