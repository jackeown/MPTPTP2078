%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
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
%$ r2_hidden > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_26,plain,
    ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_41,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_33])).

tff(c_55,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k1_relset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_55])).

tff(c_65,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_213,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(k4_tarski('#skF_1'(A_83,B_84),'#skF_2'(A_83,B_84)),A_83)
      | r2_hidden('#skF_3'(A_83,B_84),B_84)
      | k1_relat_1(A_83) = B_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k1_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(C_20,D_23),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_250,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),k1_relat_1(A_86))
      | r2_hidden('#skF_3'(A_86,B_87),B_87)
      | k1_relat_1(A_86) = B_87 ) ),
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
      | ~ m1_subset_1(k1_relat_1(A_158),k1_zfmisc_1(A_160))
      | r2_hidden('#skF_3'(A_158,B_159),B_159)
      | k1_relat_1(A_158) = B_159 ) ),
    inference(resolution,[status(thm)],[c_250,c_2])).

tff(c_1189,plain,(
    ! [B_159] :
      ( r2_hidden('#skF_1'('#skF_7',B_159),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_159),B_159)
      | k1_relat_1('#skF_7') = B_159 ) ),
    inference(resolution,[status(thm)],[c_65,c_1186])).

tff(c_32,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski(D_36,'#skF_8'(D_36)),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6')
      | k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski(D_36,'#skF_8'(D_36)),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_75,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski(D_36,'#skF_8'(D_36)),'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_74])).

tff(c_289,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden(k4_tarski('#skF_1'(A_97,B_98),'#skF_2'(A_97,B_98)),A_97)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_97,B_98),D_99),A_97)
      | k1_relat_1(A_97) = B_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_385,plain,(
    ! [B_105] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_105),'#skF_2'('#skF_7',B_105)),'#skF_7')
      | k1_relat_1('#skF_7') = B_105
      | ~ r2_hidden('#skF_3'('#skF_7',B_105),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_75,c_289])).

tff(c_393,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_1'('#skF_7',B_106),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = B_106
      | ~ r2_hidden('#skF_3'('#skF_7',B_106),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_385,c_6])).

tff(c_2669,plain,(
    ! [B_239,A_240] :
      ( r2_hidden('#skF_1'('#skF_7',B_239),A_240)
      | ~ m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1(A_240))
      | k1_relat_1('#skF_7') = B_239
      | ~ r2_hidden('#skF_3'('#skF_7',B_239),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_2673,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_1'('#skF_7',B_241),'#skF_6')
      | k1_relat_1('#skF_7') = B_241
      | ~ r2_hidden('#skF_3'('#skF_7',B_241),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_65,c_2669])).

tff(c_2685,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1189,c_2673])).

tff(c_2695,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_41,c_2685])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_3'(A_5,B_6),B_6)
      | k1_relat_1(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_5,B_6,D_19] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_5,B_6),D_19),A_5)
      | k1_relat_1(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2703,plain,(
    ! [D_19] :
      ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_19),'#skF_7')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2695,c_8])).

tff(c_2713,plain,(
    ! [D_242] : ~ r2_hidden(k4_tarski('#skF_3'('#skF_7','#skF_6'),D_242),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_2703])).

tff(c_2737,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_75,c_2713])).

tff(c_2750,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_2737])).

tff(c_2759,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2695,c_2750])).

tff(c_2761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_2759])).

tff(c_2762,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2763,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2778,plain,(
    ! [A_251,B_252,C_253] :
      ( k1_relset_1(A_251,B_252,C_253) = k1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2781,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_2778])).

tff(c_2783,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_2781])).

tff(c_2808,plain,(
    ! [C_259,A_260] :
      ( r2_hidden(k4_tarski(C_259,'#skF_4'(A_260,k1_relat_1(A_260),C_259)),A_260)
      | ~ r2_hidden(C_259,k1_relat_1(A_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [E_39] :
      ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski('#skF_9',E_39),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2775,plain,(
    ! [E_39] : ~ r2_hidden(k4_tarski('#skF_9',E_39),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_22])).

tff(c_2812,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2808,c_2775])).

tff(c_2824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2783,c_2812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.95  
% 4.99/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.95  %$ r2_hidden > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1
% 4.99/1.95  
% 4.99/1.95  %Foreground sorts:
% 4.99/1.95  
% 4.99/1.95  
% 4.99/1.95  %Background operators:
% 4.99/1.95  
% 4.99/1.95  
% 4.99/1.95  %Foreground operators:
% 4.99/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.99/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.99/1.95  tff('#skF_8', type, '#skF_8': $i > $i).
% 4.99/1.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.99/1.95  tff('#skF_7', type, '#skF_7': $i).
% 4.99/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.99/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.99/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.99/1.95  tff('#skF_9', type, '#skF_9': $i).
% 4.99/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.99/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.99/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.99/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.99/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.99/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.99/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.99/1.95  
% 4.99/1.97  tff(f_61, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.99/1.97  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.99/1.97  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.99/1.97  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.99/1.97  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.99/1.97  tff(c_20, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.99/1.97  tff(c_36, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.99/1.97  tff(c_40, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_36])).
% 4.99/1.97  tff(c_26, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.99/1.97  tff(c_33, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_26])).
% 4.99/1.97  tff(c_41, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_33])).
% 4.99/1.97  tff(c_55, plain, (![A_52, B_53, C_54]: (m1_subset_1(k1_relset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.99/1.97  tff(c_62, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_55])).
% 4.99/1.97  tff(c_65, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 4.99/1.97  tff(c_213, plain, (![A_83, B_84]: (r2_hidden(k4_tarski('#skF_1'(A_83, B_84), '#skF_2'(A_83, B_84)), A_83) | r2_hidden('#skF_3'(A_83, B_84), B_84) | k1_relat_1(A_83)=B_84)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_6, plain, (![C_20, A_5, D_23]: (r2_hidden(C_20, k1_relat_1(A_5)) | ~r2_hidden(k4_tarski(C_20, D_23), A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_250, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), k1_relat_1(A_86)) | r2_hidden('#skF_3'(A_86, B_87), B_87) | k1_relat_1(A_86)=B_87)), inference(resolution, [status(thm)], [c_213, c_6])).
% 4.99/1.97  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/1.97  tff(c_1186, plain, (![A_158, B_159, A_160]: (r2_hidden('#skF_1'(A_158, B_159), A_160) | ~m1_subset_1(k1_relat_1(A_158), k1_zfmisc_1(A_160)) | r2_hidden('#skF_3'(A_158, B_159), B_159) | k1_relat_1(A_158)=B_159)), inference(resolution, [status(thm)], [c_250, c_2])).
% 4.99/1.97  tff(c_1189, plain, (![B_159]: (r2_hidden('#skF_1'('#skF_7', B_159), '#skF_6') | r2_hidden('#skF_3'('#skF_7', B_159), B_159) | k1_relat_1('#skF_7')=B_159)), inference(resolution, [status(thm)], [c_65, c_1186])).
% 4.99/1.97  tff(c_32, plain, (![D_36]: (r2_hidden(k4_tarski(D_36, '#skF_8'(D_36)), '#skF_7') | ~r2_hidden(D_36, '#skF_6') | k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.99/1.97  tff(c_74, plain, (![D_36]: (r2_hidden(k4_tarski(D_36, '#skF_8'(D_36)), '#skF_7') | ~r2_hidden(D_36, '#skF_6') | k1_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 4.99/1.97  tff(c_75, plain, (![D_36]: (r2_hidden(k4_tarski(D_36, '#skF_8'(D_36)), '#skF_7') | ~r2_hidden(D_36, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_41, c_74])).
% 4.99/1.97  tff(c_289, plain, (![A_97, B_98, D_99]: (r2_hidden(k4_tarski('#skF_1'(A_97, B_98), '#skF_2'(A_97, B_98)), A_97) | ~r2_hidden(k4_tarski('#skF_3'(A_97, B_98), D_99), A_97) | k1_relat_1(A_97)=B_98)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_385, plain, (![B_105]: (r2_hidden(k4_tarski('#skF_1'('#skF_7', B_105), '#skF_2'('#skF_7', B_105)), '#skF_7') | k1_relat_1('#skF_7')=B_105 | ~r2_hidden('#skF_3'('#skF_7', B_105), '#skF_6'))), inference(resolution, [status(thm)], [c_75, c_289])).
% 4.99/1.97  tff(c_393, plain, (![B_106]: (r2_hidden('#skF_1'('#skF_7', B_106), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=B_106 | ~r2_hidden('#skF_3'('#skF_7', B_106), '#skF_6'))), inference(resolution, [status(thm)], [c_385, c_6])).
% 4.99/1.97  tff(c_2669, plain, (![B_239, A_240]: (r2_hidden('#skF_1'('#skF_7', B_239), A_240) | ~m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1(A_240)) | k1_relat_1('#skF_7')=B_239 | ~r2_hidden('#skF_3'('#skF_7', B_239), '#skF_6'))), inference(resolution, [status(thm)], [c_393, c_2])).
% 4.99/1.97  tff(c_2673, plain, (![B_241]: (r2_hidden('#skF_1'('#skF_7', B_241), '#skF_6') | k1_relat_1('#skF_7')=B_241 | ~r2_hidden('#skF_3'('#skF_7', B_241), '#skF_6'))), inference(resolution, [status(thm)], [c_65, c_2669])).
% 4.99/1.97  tff(c_2685, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_1189, c_2673])).
% 4.99/1.97  tff(c_2695, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_41, c_41, c_2685])).
% 4.99/1.97  tff(c_12, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r2_hidden('#skF_3'(A_5, B_6), B_6) | k1_relat_1(A_5)=B_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_8, plain, (![A_5, B_6, D_19]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | ~r2_hidden(k4_tarski('#skF_3'(A_5, B_6), D_19), A_5) | k1_relat_1(A_5)=B_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_2703, plain, (![D_19]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_19), '#skF_7') | k1_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_2695, c_8])).
% 4.99/1.97  tff(c_2713, plain, (![D_242]: (~r2_hidden(k4_tarski('#skF_3'('#skF_7', '#skF_6'), D_242), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_41, c_2703])).
% 4.99/1.97  tff(c_2737, plain, (~r2_hidden('#skF_3'('#skF_7', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_75, c_2713])).
% 4.99/1.97  tff(c_2750, plain, (~r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_12, c_2737])).
% 4.99/1.97  tff(c_2759, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2695, c_2750])).
% 4.99/1.97  tff(c_2761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_2759])).
% 4.99/1.97  tff(c_2762, plain, (r2_hidden('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 4.99/1.97  tff(c_2763, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 4.99/1.97  tff(c_2778, plain, (![A_251, B_252, C_253]: (k1_relset_1(A_251, B_252, C_253)=k1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.99/1.97  tff(c_2781, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_2778])).
% 4.99/1.97  tff(c_2783, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_2781])).
% 4.99/1.97  tff(c_2808, plain, (![C_259, A_260]: (r2_hidden(k4_tarski(C_259, '#skF_4'(A_260, k1_relat_1(A_260), C_259)), A_260) | ~r2_hidden(C_259, k1_relat_1(A_260)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/1.97  tff(c_22, plain, (![E_39]: (k1_relset_1('#skF_6', '#skF_5', '#skF_7')!='#skF_6' | ~r2_hidden(k4_tarski('#skF_9', E_39), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.99/1.97  tff(c_2775, plain, (![E_39]: (~r2_hidden(k4_tarski('#skF_9', E_39), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_22])).
% 4.99/1.97  tff(c_2812, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2808, c_2775])).
% 4.99/1.97  tff(c_2824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2783, c_2812])).
% 4.99/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.97  
% 4.99/1.97  Inference rules
% 4.99/1.97  ----------------------
% 4.99/1.97  #Ref     : 0
% 4.99/1.97  #Sup     : 651
% 4.99/1.97  #Fact    : 0
% 4.99/1.97  #Define  : 0
% 4.99/1.97  #Split   : 16
% 4.99/1.97  #Chain   : 0
% 4.99/1.97  #Close   : 0
% 4.99/1.97  
% 4.99/1.97  Ordering : KBO
% 4.99/1.97  
% 4.99/1.97  Simplification rules
% 4.99/1.97  ----------------------
% 4.99/1.97  #Subsume      : 82
% 4.99/1.97  #Demod        : 24
% 4.99/1.97  #Tautology    : 36
% 4.99/1.97  #SimpNegUnit  : 8
% 4.99/1.97  #BackRed      : 1
% 4.99/1.97  
% 4.99/1.97  #Partial instantiations: 0
% 4.99/1.97  #Strategies tried      : 1
% 4.99/1.97  
% 4.99/1.97  Timing (in seconds)
% 4.99/1.97  ----------------------
% 4.99/1.97  Preprocessing        : 0.29
% 4.99/1.97  Parsing              : 0.15
% 4.99/1.97  CNF conversion       : 0.02
% 4.99/1.97  Main loop            : 0.90
% 4.99/1.97  Inferencing          : 0.29
% 4.99/1.97  Reduction            : 0.21
% 4.99/1.97  Demodulation         : 0.13
% 4.99/1.97  BG Simplification    : 0.04
% 4.99/1.97  Subsumption          : 0.29
% 4.99/1.97  Abstraction          : 0.05
% 4.99/1.97  MUC search           : 0.00
% 4.99/1.97  Cooper               : 0.00
% 4.99/1.97  Total                : 1.22
% 4.99/1.97  Index Insertion      : 0.00
% 4.99/1.97  Index Deletion       : 0.00
% 4.99/1.97  Index Matching       : 0.00
% 4.99/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
