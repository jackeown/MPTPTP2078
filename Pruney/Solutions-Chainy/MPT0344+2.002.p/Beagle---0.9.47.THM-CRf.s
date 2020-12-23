%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 256 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 ( 608 expanded)
%              Number of equality atoms :   21 ( 105 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [C_22] :
      ( ~ r2_hidden(C_22,'#skF_7')
      | ~ m1_subset_1(C_22,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_127,plain,(
    ! [B_40] :
      ( ~ m1_subset_1(B_40,'#skF_6')
      | ~ m1_subset_1(B_40,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_114,c_40])).

tff(c_215,plain,(
    ! [B_58] :
      ( ~ m1_subset_1(B_58,'#skF_6')
      | ~ m1_subset_1(B_58,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_225,plain,(
    ! [B_20] :
      ( ~ m1_subset_1(B_20,'#skF_6')
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_36,c_215])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [C_29] :
      ( ~ r2_hidden(C_29,'#skF_7')
      | ~ m1_subset_1(C_29,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_67,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_71,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_67])).

tff(c_129,plain,(
    ! [B_42,A_43] :
      ( m1_subset_1(B_42,A_43)
      | ~ r2_hidden(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_145,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_3'(A_10),A_10)
      | v1_xboole_0(A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_84,plain,(
    ! [B_32,A_33] :
      ( m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(B_32)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_71])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_103,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1095,plain,(
    ! [B_137,A_138] :
      ( r1_tarski(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_138))
      | v1_xboole_0(k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_114,c_20])).

tff(c_1120,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_1095])).

tff(c_1130,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1120])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(B_20,A_19)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_227,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1759,plain,(
    ! [B_163,B_164,A_165] :
      ( r2_hidden(B_163,B_164)
      | ~ r1_tarski(A_165,B_164)
      | ~ m1_subset_1(B_163,A_165)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_34,c_227])).

tff(c_1767,plain,(
    ! [B_163] :
      ( r2_hidden(B_163,'#skF_6')
      | ~ m1_subset_1(B_163,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1130,c_1759])).

tff(c_1810,plain,(
    ! [B_166] :
      ( r2_hidden(B_166,'#skF_6')
      | ~ m1_subset_1(B_166,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_1767])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,A_19)
      | ~ r2_hidden(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1822,plain,(
    ! [B_166] :
      ( m1_subset_1(B_166,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_166,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1810,c_32])).

tff(c_1833,plain,(
    ! [B_167] :
      ( m1_subset_1(B_167,'#skF_6')
      | ~ m1_subset_1(B_167,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1822])).

tff(c_1841,plain,
    ( m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_145,c_1833])).

tff(c_1856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_226,c_71,c_1841])).

tff(c_1858,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_48,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_3'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_1863,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1858,c_52])).

tff(c_1868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1863])).

tff(c_1869,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_1873,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1869,c_52])).

tff(c_1877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1873])).

tff(c_1879,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1883,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1879,c_52])).

tff(c_1886,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_42])).

tff(c_1891,plain,(
    ! [B_168,A_169] :
      ( v1_xboole_0(B_168)
      | ~ m1_subset_1(B_168,A_169)
      | ~ v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1899,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_1891])).

tff(c_1906,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1899])).

tff(c_1941,plain,(
    ! [B_178,A_179] :
      ( r2_hidden(B_178,A_179)
      | ~ m1_subset_1(B_178,A_179)
      | v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2808,plain,(
    ! [B_252,A_253] :
      ( r1_tarski(B_252,A_253)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(A_253))
      | v1_xboole_0(k1_zfmisc_1(A_253)) ) ),
    inference(resolution,[status(thm)],[c_1941,c_20])).

tff(c_2836,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_2808])).

tff(c_2849,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1906,c_2836])).

tff(c_1885,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_12])).

tff(c_2050,plain,(
    ! [C_196,B_197,A_198] :
      ( r2_hidden(C_196,B_197)
      | ~ r2_hidden(C_196,A_198)
      | ~ r1_tarski(A_198,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2453,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_3'(A_224),B_225)
      | ~ r1_tarski(A_224,B_225)
      | A_224 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1885,c_2050])).

tff(c_2474,plain,(
    ! [B_225,A_224] :
      ( ~ v1_xboole_0(B_225)
      | ~ r1_tarski(A_224,B_225)
      | A_224 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2453,c_2])).

tff(c_2852,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2849,c_2474])).

tff(c_2863,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_2852])).

tff(c_2865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1886,c_2863])).

tff(c_2866,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1899])).

tff(c_1884,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(A_26)
      | A_26 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_52])).

tff(c_2870,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2866,c_1884])).

tff(c_2874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1886,c_2870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.73  
% 4.00/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.73  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 4.00/1.73  
% 4.00/1.73  %Foreground sorts:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Background operators:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Foreground operators:
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.00/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.00/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.00/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.73  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.00/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.00/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.00/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.73  
% 4.35/1.76  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.35/1.76  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.35/1.76  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.35/1.76  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.35/1.76  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.35/1.76  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.35/1.76  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.76  tff(c_36, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~v1_xboole_0(B_20) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_114, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | ~m1_subset_1(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_40, plain, (![C_22]: (~r2_hidden(C_22, '#skF_7') | ~m1_subset_1(C_22, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.76  tff(c_127, plain, (![B_40]: (~m1_subset_1(B_40, '#skF_6') | ~m1_subset_1(B_40, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_114, c_40])).
% 4.35/1.76  tff(c_215, plain, (![B_58]: (~m1_subset_1(B_58, '#skF_6') | ~m1_subset_1(B_58, '#skF_7'))), inference(splitLeft, [status(thm)], [c_127])).
% 4.35/1.76  tff(c_225, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_6') | ~v1_xboole_0(B_20) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_36, c_215])).
% 4.35/1.76  tff(c_226, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_225])).
% 4.35/1.76  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.35/1.76  tff(c_59, plain, (![C_29]: (~r2_hidden(C_29, '#skF_7') | ~m1_subset_1(C_29, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.76  tff(c_67, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_12, c_59])).
% 4.35/1.76  tff(c_71, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_67])).
% 4.35/1.76  tff(c_129, plain, (![B_42, A_43]: (m1_subset_1(B_42, A_43) | ~r2_hidden(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_145, plain, (![A_10]: (m1_subset_1('#skF_3'(A_10), A_10) | v1_xboole_0(A_10) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_12, c_129])).
% 4.35/1.76  tff(c_84, plain, (![B_32, A_33]: (m1_subset_1(B_32, A_33) | ~v1_xboole_0(B_32) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_92, plain, (~v1_xboole_0('#skF_3'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_84, c_71])).
% 4.35/1.76  tff(c_93, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_92])).
% 4.35/1.76  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.35/1.76  tff(c_94, plain, (![B_34, A_35]: (v1_xboole_0(B_34) | ~m1_subset_1(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_102, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_94])).
% 4.35/1.76  tff(c_103, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_102])).
% 4.35/1.76  tff(c_20, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.35/1.76  tff(c_1095, plain, (![B_137, A_138]: (r1_tarski(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(A_138)) | v1_xboole_0(k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_114, c_20])).
% 4.35/1.76  tff(c_1120, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1095])).
% 4.35/1.76  tff(c_1130, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_103, c_1120])).
% 4.35/1.76  tff(c_34, plain, (![B_20, A_19]: (r2_hidden(B_20, A_19) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_227, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.35/1.76  tff(c_1759, plain, (![B_163, B_164, A_165]: (r2_hidden(B_163, B_164) | ~r1_tarski(A_165, B_164) | ~m1_subset_1(B_163, A_165) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_34, c_227])).
% 4.35/1.76  tff(c_1767, plain, (![B_163]: (r2_hidden(B_163, '#skF_6') | ~m1_subset_1(B_163, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_1130, c_1759])).
% 4.35/1.76  tff(c_1810, plain, (![B_166]: (r2_hidden(B_166, '#skF_6') | ~m1_subset_1(B_166, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_226, c_1767])).
% 4.35/1.76  tff(c_32, plain, (![B_20, A_19]: (m1_subset_1(B_20, A_19) | ~r2_hidden(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_1822, plain, (![B_166]: (m1_subset_1(B_166, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_166, '#skF_7'))), inference(resolution, [status(thm)], [c_1810, c_32])).
% 4.35/1.76  tff(c_1833, plain, (![B_167]: (m1_subset_1(B_167, '#skF_6') | ~m1_subset_1(B_167, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_93, c_1822])).
% 4.35/1.76  tff(c_1841, plain, (m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_145, c_1833])).
% 4.35/1.76  tff(c_1856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_226, c_71, c_1841])).
% 4.35/1.76  tff(c_1858, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_225])).
% 4.35/1.76  tff(c_48, plain, (![A_26]: (r2_hidden('#skF_3'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.35/1.76  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.76  tff(c_52, plain, (![A_26]: (~v1_xboole_0(A_26) | k1_xboole_0=A_26)), inference(resolution, [status(thm)], [c_48, c_2])).
% 4.35/1.76  tff(c_1863, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1858, c_52])).
% 4.35/1.76  tff(c_1868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1863])).
% 4.35/1.76  tff(c_1869, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_102])).
% 4.35/1.76  tff(c_1873, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1869, c_52])).
% 4.35/1.76  tff(c_1877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1873])).
% 4.35/1.76  tff(c_1879, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_92])).
% 4.35/1.76  tff(c_1883, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1879, c_52])).
% 4.35/1.76  tff(c_1886, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_42])).
% 4.35/1.76  tff(c_1891, plain, (![B_168, A_169]: (v1_xboole_0(B_168) | ~m1_subset_1(B_168, A_169) | ~v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_1899, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1891])).
% 4.35/1.76  tff(c_1906, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1899])).
% 4.35/1.76  tff(c_1941, plain, (![B_178, A_179]: (r2_hidden(B_178, A_179) | ~m1_subset_1(B_178, A_179) | v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.35/1.76  tff(c_2808, plain, (![B_252, A_253]: (r1_tarski(B_252, A_253) | ~m1_subset_1(B_252, k1_zfmisc_1(A_253)) | v1_xboole_0(k1_zfmisc_1(A_253)))), inference(resolution, [status(thm)], [c_1941, c_20])).
% 4.35/1.76  tff(c_2836, plain, (r1_tarski('#skF_7', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_2808])).
% 4.35/1.76  tff(c_2849, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1906, c_2836])).
% 4.35/1.76  tff(c_1885, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_12])).
% 4.35/1.76  tff(c_2050, plain, (![C_196, B_197, A_198]: (r2_hidden(C_196, B_197) | ~r2_hidden(C_196, A_198) | ~r1_tarski(A_198, B_197))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.35/1.76  tff(c_2453, plain, (![A_224, B_225]: (r2_hidden('#skF_3'(A_224), B_225) | ~r1_tarski(A_224, B_225) | A_224='#skF_6')), inference(resolution, [status(thm)], [c_1885, c_2050])).
% 4.35/1.76  tff(c_2474, plain, (![B_225, A_224]: (~v1_xboole_0(B_225) | ~r1_tarski(A_224, B_225) | A_224='#skF_6')), inference(resolution, [status(thm)], [c_2453, c_2])).
% 4.35/1.76  tff(c_2852, plain, (~v1_xboole_0('#skF_6') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2849, c_2474])).
% 4.35/1.76  tff(c_2863, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1879, c_2852])).
% 4.35/1.76  tff(c_2865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1886, c_2863])).
% 4.35/1.76  tff(c_2866, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1899])).
% 4.35/1.76  tff(c_1884, plain, (![A_26]: (~v1_xboole_0(A_26) | A_26='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_52])).
% 4.35/1.76  tff(c_2870, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2866, c_1884])).
% 4.35/1.76  tff(c_2874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1886, c_2870])).
% 4.35/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.76  
% 4.35/1.76  Inference rules
% 4.35/1.76  ----------------------
% 4.35/1.76  #Ref     : 0
% 4.35/1.76  #Sup     : 647
% 4.35/1.76  #Fact    : 0
% 4.35/1.76  #Define  : 0
% 4.35/1.76  #Split   : 13
% 4.35/1.76  #Chain   : 0
% 4.35/1.76  #Close   : 0
% 4.35/1.76  
% 4.35/1.76  Ordering : KBO
% 4.35/1.76  
% 4.35/1.76  Simplification rules
% 4.35/1.76  ----------------------
% 4.35/1.76  #Subsume      : 214
% 4.35/1.76  #Demod        : 136
% 4.35/1.76  #Tautology    : 151
% 4.35/1.76  #SimpNegUnit  : 90
% 4.35/1.76  #BackRed      : 25
% 4.35/1.76  
% 4.35/1.76  #Partial instantiations: 0
% 4.35/1.76  #Strategies tried      : 1
% 4.35/1.76  
% 4.35/1.76  Timing (in seconds)
% 4.35/1.76  ----------------------
% 4.35/1.76  Preprocessing        : 0.29
% 4.35/1.76  Parsing              : 0.15
% 4.35/1.76  CNF conversion       : 0.02
% 4.35/1.76  Main loop            : 0.70
% 4.35/1.76  Inferencing          : 0.25
% 4.35/1.76  Reduction            : 0.17
% 4.35/1.76  Demodulation         : 0.11
% 4.35/1.76  BG Simplification    : 0.03
% 4.35/1.76  Subsumption          : 0.18
% 4.35/1.76  Abstraction          : 0.03
% 4.35/1.76  MUC search           : 0.00
% 4.35/1.76  Cooper               : 0.00
% 4.35/1.76  Total                : 1.04
% 4.35/1.76  Index Insertion      : 0.00
% 4.35/1.76  Index Deletion       : 0.00
% 4.35/1.76  Index Matching       : 0.00
% 4.35/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
