%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 207 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 503 expanded)
%              Number of equality atoms :   15 (  67 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_166,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [C_21] :
      ( ~ r2_hidden(C_21,'#skF_7')
      | ~ m1_subset_1(C_21,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,(
    ! [B_48] :
      ( ~ m1_subset_1(B_48,'#skF_6')
      | ~ m1_subset_1(B_48,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_166,c_36])).

tff(c_220,plain,(
    ! [B_55] :
      ( ~ m1_subset_1(B_55,'#skF_6')
      | ~ m1_subset_1(B_55,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_230,plain,(
    ! [B_18] :
      ( ~ m1_subset_1(B_18,'#skF_6')
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_220])).

tff(c_231,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_54,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_3'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_36])).

tff(c_64,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_58])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_3'(A_10),A_10)
      | v1_xboole_0(A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_73,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(B_31)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_7'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_73,c_64])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ! [B_48,A_12] :
      ( r1_tarski(B_48,A_12)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_166,c_14])).

tff(c_193,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_177])).

tff(c_213,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_193])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r2_hidden(B_18,A_17)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_233,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_994,plain,(
    ! [B_137,B_138,A_139] :
      ( r2_hidden(B_137,B_138)
      | ~ r1_tarski(A_139,B_138)
      | ~ m1_subset_1(B_137,A_139)
      | v1_xboole_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_28,c_233])).

tff(c_1016,plain,(
    ! [B_137] :
      ( r2_hidden(B_137,'#skF_6')
      | ~ m1_subset_1(B_137,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_213,c_994])).

tff(c_1040,plain,(
    ! [B_140] :
      ( r2_hidden(B_140,'#skF_6')
      | ~ m1_subset_1(B_140,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_1016])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ r2_hidden(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1052,plain,(
    ! [B_140] :
      ( m1_subset_1(B_140,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_140,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1040,c_26])).

tff(c_1063,plain,(
    ! [B_141] :
      ( m1_subset_1(B_141,'#skF_6')
      | ~ m1_subset_1(B_141,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1052])).

tff(c_1071,plain,
    ( m1_subset_1('#skF_3'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_123,c_1063])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_231,c_64,c_1071])).

tff(c_1088,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_1091,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1088,c_65])).

tff(c_1095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1091])).

tff(c_1097,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1101,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1097,c_65])).

tff(c_1104,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_38])).

tff(c_1179,plain,(
    ! [B_156,A_157] :
      ( r2_hidden(B_156,A_157)
      | ~ m1_subset_1(B_156,A_157)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1199,plain,(
    ! [B_156] :
      ( ~ m1_subset_1(B_156,'#skF_6')
      | ~ m1_subset_1(B_156,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1179,c_36])).

tff(c_1264,plain,(
    ! [B_167] :
      ( ~ m1_subset_1(B_167,'#skF_6')
      | ~ m1_subset_1(B_167,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1274,plain,(
    ! [B_18] :
      ( ~ m1_subset_1(B_18,'#skF_6')
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_1264])).

tff(c_1275,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1274])).

tff(c_1187,plain,(
    ! [B_156,A_12] :
      ( r1_tarski(B_156,A_12)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_1179,c_14])).

tff(c_1201,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(B_158,A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1187])).

tff(c_1210,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_1201])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1276,plain,(
    ! [C_168,B_169,A_170] :
      ( r2_hidden(C_168,B_169)
      | ~ r2_hidden(C_168,A_170)
      | ~ r1_tarski(A_170,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1310,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173),B_174)
      | ~ r1_tarski(A_173,B_174)
      | v1_xboole_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_4,c_1276])).

tff(c_1345,plain,(
    ! [B_176,A_177] :
      ( ~ v1_xboole_0(B_176)
      | ~ r1_tarski(A_177,B_176)
      | v1_xboole_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_1310,c_2])).

tff(c_1351,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1210,c_1345])).

tff(c_1364,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1351])).

tff(c_1366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1275,c_1364])).

tff(c_1368,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1274])).

tff(c_1102,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(A_27)
      | A_27 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_65])).

tff(c_1371,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1368,c_1102])).

tff(c_1375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1104,c_1371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.59  
% 3.45/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 3.45/1.60  
% 3.45/1.60  %Foreground sorts:
% 3.45/1.60  
% 3.45/1.60  
% 3.45/1.60  %Background operators:
% 3.45/1.60  
% 3.45/1.60  
% 3.45/1.60  %Foreground operators:
% 3.45/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.45/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.45/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.45/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.45/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.45/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.60  
% 3.45/1.62  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.45/1.62  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.45/1.62  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.45/1.62  tff(f_69, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.45/1.62  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.45/1.62  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.45/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.45/1.62  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.45/1.62  tff(c_30, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_166, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_36, plain, (![C_21]: (~r2_hidden(C_21, '#skF_7') | ~m1_subset_1(C_21, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.45/1.62  tff(c_190, plain, (![B_48]: (~m1_subset_1(B_48, '#skF_6') | ~m1_subset_1(B_48, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_166, c_36])).
% 3.45/1.62  tff(c_220, plain, (![B_55]: (~m1_subset_1(B_55, '#skF_6') | ~m1_subset_1(B_55, '#skF_7'))), inference(splitLeft, [status(thm)], [c_190])).
% 3.45/1.62  tff(c_230, plain, (![B_18]: (~m1_subset_1(B_18, '#skF_6') | ~v1_xboole_0(B_18) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_220])).
% 3.45/1.62  tff(c_231, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_230])).
% 3.45/1.62  tff(c_54, plain, (![A_27]: (r2_hidden('#skF_3'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.62  tff(c_58, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_54, c_36])).
% 3.45/1.62  tff(c_64, plain, (~m1_subset_1('#skF_3'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_58])).
% 3.45/1.62  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.62  tff(c_110, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_123, plain, (![A_10]: (m1_subset_1('#skF_3'(A_10), A_10) | v1_xboole_0(A_10) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_12, c_110])).
% 3.45/1.62  tff(c_73, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~v1_xboole_0(B_31) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_85, plain, (~v1_xboole_0('#skF_3'('#skF_7')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_73, c_64])).
% 3.45/1.62  tff(c_86, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_85])).
% 3.45/1.62  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.45/1.62  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.45/1.62  tff(c_14, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.62  tff(c_177, plain, (![B_48, A_12]: (r1_tarski(B_48, A_12) | ~m1_subset_1(B_48, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_166, c_14])).
% 3.45/1.62  tff(c_193, plain, (![B_52, A_53]: (r1_tarski(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_34, c_177])).
% 3.45/1.62  tff(c_213, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_193])).
% 3.45/1.62  tff(c_28, plain, (![B_18, A_17]: (r2_hidden(B_18, A_17) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_233, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.62  tff(c_994, plain, (![B_137, B_138, A_139]: (r2_hidden(B_137, B_138) | ~r1_tarski(A_139, B_138) | ~m1_subset_1(B_137, A_139) | v1_xboole_0(A_139))), inference(resolution, [status(thm)], [c_28, c_233])).
% 3.45/1.62  tff(c_1016, plain, (![B_137]: (r2_hidden(B_137, '#skF_6') | ~m1_subset_1(B_137, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_213, c_994])).
% 3.45/1.62  tff(c_1040, plain, (![B_140]: (r2_hidden(B_140, '#skF_6') | ~m1_subset_1(B_140, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_231, c_1016])).
% 3.45/1.62  tff(c_26, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~r2_hidden(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_1052, plain, (![B_140]: (m1_subset_1(B_140, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(B_140, '#skF_7'))), inference(resolution, [status(thm)], [c_1040, c_26])).
% 3.45/1.62  tff(c_1063, plain, (![B_141]: (m1_subset_1(B_141, '#skF_6') | ~m1_subset_1(B_141, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_1052])).
% 3.45/1.62  tff(c_1071, plain, (m1_subset_1('#skF_3'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_123, c_1063])).
% 3.45/1.62  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_231, c_64, c_1071])).
% 3.45/1.62  tff(c_1088, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_230])).
% 3.45/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.62  tff(c_65, plain, (![A_27]: (~v1_xboole_0(A_27) | k1_xboole_0=A_27)), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.45/1.62  tff(c_1091, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1088, c_65])).
% 3.45/1.62  tff(c_1095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1091])).
% 3.45/1.62  tff(c_1097, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 3.45/1.62  tff(c_1101, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1097, c_65])).
% 3.45/1.62  tff(c_1104, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_38])).
% 3.45/1.62  tff(c_1179, plain, (![B_156, A_157]: (r2_hidden(B_156, A_157) | ~m1_subset_1(B_156, A_157) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.62  tff(c_1199, plain, (![B_156]: (~m1_subset_1(B_156, '#skF_6') | ~m1_subset_1(B_156, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_1179, c_36])).
% 3.45/1.62  tff(c_1264, plain, (![B_167]: (~m1_subset_1(B_167, '#skF_6') | ~m1_subset_1(B_167, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1199])).
% 3.45/1.62  tff(c_1274, plain, (![B_18]: (~m1_subset_1(B_18, '#skF_6') | ~v1_xboole_0(B_18) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_30, c_1264])).
% 3.45/1.62  tff(c_1275, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1274])).
% 3.45/1.62  tff(c_1187, plain, (![B_156, A_12]: (r1_tarski(B_156, A_12) | ~m1_subset_1(B_156, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_1179, c_14])).
% 3.45/1.62  tff(c_1201, plain, (![B_158, A_159]: (r1_tarski(B_158, A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)))), inference(negUnitSimplification, [status(thm)], [c_34, c_1187])).
% 3.45/1.62  tff(c_1210, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_1201])).
% 3.45/1.62  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.62  tff(c_1276, plain, (![C_168, B_169, A_170]: (r2_hidden(C_168, B_169) | ~r2_hidden(C_168, A_170) | ~r1_tarski(A_170, B_169))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.45/1.62  tff(c_1310, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173), B_174) | ~r1_tarski(A_173, B_174) | v1_xboole_0(A_173))), inference(resolution, [status(thm)], [c_4, c_1276])).
% 3.45/1.62  tff(c_1345, plain, (![B_176, A_177]: (~v1_xboole_0(B_176) | ~r1_tarski(A_177, B_176) | v1_xboole_0(A_177))), inference(resolution, [status(thm)], [c_1310, c_2])).
% 3.45/1.62  tff(c_1351, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1210, c_1345])).
% 3.45/1.62  tff(c_1364, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1351])).
% 3.45/1.62  tff(c_1366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1275, c_1364])).
% 3.45/1.62  tff(c_1368, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1274])).
% 3.45/1.62  tff(c_1102, plain, (![A_27]: (~v1_xboole_0(A_27) | A_27='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_65])).
% 3.45/1.62  tff(c_1371, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1368, c_1102])).
% 3.45/1.62  tff(c_1375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1104, c_1371])).
% 3.45/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.62  
% 3.45/1.62  Inference rules
% 3.45/1.62  ----------------------
% 3.45/1.62  #Ref     : 0
% 3.45/1.62  #Sup     : 274
% 3.45/1.62  #Fact    : 0
% 3.45/1.62  #Define  : 0
% 3.45/1.62  #Split   : 10
% 3.45/1.62  #Chain   : 0
% 3.45/1.62  #Close   : 0
% 3.45/1.62  
% 3.45/1.62  Ordering : KBO
% 3.45/1.62  
% 3.45/1.62  Simplification rules
% 3.45/1.62  ----------------------
% 3.45/1.62  #Subsume      : 112
% 3.45/1.62  #Demod        : 26
% 3.45/1.62  #Tautology    : 45
% 3.45/1.62  #SimpNegUnit  : 63
% 3.45/1.62  #BackRed      : 21
% 3.45/1.62  
% 3.45/1.62  #Partial instantiations: 0
% 3.45/1.62  #Strategies tried      : 1
% 3.45/1.62  
% 3.45/1.62  Timing (in seconds)
% 3.45/1.62  ----------------------
% 3.45/1.62  Preprocessing        : 0.31
% 3.45/1.62  Parsing              : 0.16
% 3.45/1.62  CNF conversion       : 0.02
% 3.45/1.62  Main loop            : 0.52
% 3.45/1.62  Inferencing          : 0.21
% 3.45/1.62  Reduction            : 0.13
% 3.45/1.62  Demodulation         : 0.07
% 3.45/1.62  BG Simplification    : 0.03
% 3.45/1.62  Subsumption          : 0.12
% 3.45/1.62  Abstraction          : 0.02
% 3.45/1.62  MUC search           : 0.00
% 3.45/1.62  Cooper               : 0.00
% 3.45/1.62  Total                : 0.87
% 3.45/1.62  Index Insertion      : 0.00
% 3.45/1.62  Index Deletion       : 0.00
% 3.45/1.62  Index Matching       : 0.00
% 3.45/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
