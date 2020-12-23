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
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 274 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 ( 686 expanded)
%              Number of equality atoms :   11 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(B_34)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [C_26] :
      ( ~ r2_hidden(C_26,'#skF_6')
      | ~ m1_subset_1(C_26,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_55,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_87,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_55])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_123,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_1'(A_43),A_43)
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_89,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [C_20] :
      ( ~ r2_hidden(C_20,'#skF_6')
      | ~ m1_subset_1(C_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    ! [B_36] :
      ( ~ m1_subset_1(B_36,'#skF_5')
      | ~ m1_subset_1(B_36,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_89,c_36])).

tff(c_116,plain,(
    ! [B_36] :
      ( ~ m1_subset_1(B_36,'#skF_5')
      | ~ m1_subset_1(B_36,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_142,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_116])).

tff(c_152,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_142])).

tff(c_160,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_161,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_137,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [B_36,A_11] :
      ( r1_tarski(B_36,A_11)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_89,c_14])).

tff(c_106,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(B_38,A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_93])).

tff(c_115,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_106])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_213,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_661,plain,(
    ! [B_111,B_112,A_113] :
      ( r2_hidden(B_111,B_112)
      | ~ r1_tarski(A_113,B_112)
      | ~ m1_subset_1(B_111,A_113)
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_28,c_213])).

tff(c_681,plain,(
    ! [B_111] :
      ( r2_hidden(B_111,'#skF_5')
      | ~ m1_subset_1(B_111,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_115,c_661])).

tff(c_698,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,'#skF_5')
      | ~ m1_subset_1(B_114,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_681])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ r2_hidden(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_714,plain,(
    ! [B_114] :
      ( m1_subset_1(B_114,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_114,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_698,c_26])).

tff(c_726,plain,(
    ! [B_115] :
      ( m1_subset_1(B_115,'#skF_5')
      | ~ m1_subset_1(B_115,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_714])).

tff(c_762,plain,(
    ! [B_116] : ~ m1_subset_1(B_116,'#skF_6') ),
    inference(resolution,[status(thm)],[c_726,c_116])).

tff(c_770,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_137,c_762])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_770])).

tff(c_783,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_783,c_12])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_786])).

tff(c_791,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_794,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_791,c_12])).

tff(c_798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_794])).

tff(c_800,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_821,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_800,c_12])).

tff(c_823,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_38])).

tff(c_801,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(B_117,A_118)
      | ~ m1_subset_1(B_117,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_816,plain,(
    ! [B_117] :
      ( ~ m1_subset_1(B_117,'#skF_5')
      | ~ m1_subset_1(B_117,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_801,c_36])).

tff(c_835,plain,(
    ! [B_120] :
      ( ~ m1_subset_1(B_120,'#skF_5')
      | ~ m1_subset_1(B_120,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_839,plain,(
    ! [B_17] :
      ( ~ m1_subset_1(B_17,'#skF_6')
      | ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_835])).

tff(c_843,plain,(
    ! [B_121] :
      ( ~ m1_subset_1(B_121,'#skF_6')
      | ~ v1_xboole_0(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_839])).

tff(c_848,plain,(
    ! [B_17] :
      ( ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_843])).

tff(c_849,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_805,plain,(
    ! [B_117,A_11] :
      ( r1_tarski(B_117,A_11)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_801,c_14])).

tff(c_866,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_805])).

tff(c_875,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_866])).

tff(c_945,plain,(
    ! [C_136,B_137,A_138] :
      ( r2_hidden(C_136,B_137)
      | ~ r2_hidden(C_136,A_138)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_966,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_1'(A_141),B_142)
      | ~ r1_tarski(A_141,B_142)
      | v1_xboole_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_4,c_945])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1001,plain,(
    ! [B_144,A_145] :
      ( ~ v1_xboole_0(B_144)
      | ~ r1_tarski(A_145,B_144)
      | v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_966,c_2])).

tff(c_1007,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_875,c_1001])).

tff(c_1017,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1007])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_1017])).

tff(c_1021,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_822,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_12])).

tff(c_1024,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1021,c_822])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_1024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.59  
% 3.06/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.59  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.06/1.59  
% 3.06/1.59  %Foreground sorts:
% 3.06/1.59  
% 3.06/1.59  
% 3.06/1.59  %Background operators:
% 3.06/1.59  
% 3.06/1.59  
% 3.06/1.59  %Foreground operators:
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.06/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.06/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.06/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.59  
% 3.06/1.61  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.06/1.61  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.06/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.06/1.61  tff(f_65, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.06/1.61  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.06/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.06/1.61  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.06/1.61  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.61  tff(c_30, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~v1_xboole_0(B_17) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_79, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~v1_xboole_0(B_34) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.61  tff(c_49, plain, (![C_26]: (~r2_hidden(C_26, '#skF_6') | ~m1_subset_1(C_26, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.61  tff(c_54, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_49])).
% 3.06/1.61  tff(c_55, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 3.06/1.61  tff(c_87, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_79, c_55])).
% 3.06/1.61  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_87])).
% 3.06/1.61  tff(c_123, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_138, plain, (![A_43]: (m1_subset_1('#skF_1'(A_43), A_43) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_4, c_123])).
% 3.06/1.61  tff(c_89, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_36, plain, (![C_20]: (~r2_hidden(C_20, '#skF_6') | ~m1_subset_1(C_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.61  tff(c_104, plain, (![B_36]: (~m1_subset_1(B_36, '#skF_5') | ~m1_subset_1(B_36, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_89, c_36])).
% 3.06/1.61  tff(c_116, plain, (![B_36]: (~m1_subset_1(B_36, '#skF_5') | ~m1_subset_1(B_36, '#skF_6'))), inference(splitLeft, [status(thm)], [c_104])).
% 3.06/1.61  tff(c_142, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_138, c_116])).
% 3.06/1.61  tff(c_152, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_142])).
% 3.06/1.61  tff(c_160, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_152])).
% 3.06/1.61  tff(c_161, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_160])).
% 3.06/1.61  tff(c_137, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_123])).
% 3.06/1.61  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.61  tff(c_34, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.61  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.61  tff(c_93, plain, (![B_36, A_11]: (r1_tarski(B_36, A_11) | ~m1_subset_1(B_36, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_89, c_14])).
% 3.06/1.61  tff(c_106, plain, (![B_38, A_39]: (r1_tarski(B_38, A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)))), inference(negUnitSimplification, [status(thm)], [c_34, c_93])).
% 3.06/1.61  tff(c_115, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_106])).
% 3.06/1.61  tff(c_28, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_213, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.61  tff(c_661, plain, (![B_111, B_112, A_113]: (r2_hidden(B_111, B_112) | ~r1_tarski(A_113, B_112) | ~m1_subset_1(B_111, A_113) | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_28, c_213])).
% 3.06/1.61  tff(c_681, plain, (![B_111]: (r2_hidden(B_111, '#skF_5') | ~m1_subset_1(B_111, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_115, c_661])).
% 3.06/1.61  tff(c_698, plain, (![B_114]: (r2_hidden(B_114, '#skF_5') | ~m1_subset_1(B_114, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_161, c_681])).
% 3.06/1.61  tff(c_26, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~r2_hidden(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_714, plain, (![B_114]: (m1_subset_1(B_114, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_114, '#skF_6'))), inference(resolution, [status(thm)], [c_698, c_26])).
% 3.06/1.61  tff(c_726, plain, (![B_115]: (m1_subset_1(B_115, '#skF_5') | ~m1_subset_1(B_115, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_88, c_714])).
% 3.06/1.61  tff(c_762, plain, (![B_116]: (~m1_subset_1(B_116, '#skF_6'))), inference(resolution, [status(thm)], [c_726, c_116])).
% 3.06/1.61  tff(c_770, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_137, c_762])).
% 3.06/1.61  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_770])).
% 3.06/1.61  tff(c_783, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_160])).
% 3.06/1.61  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.61  tff(c_786, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_783, c_12])).
% 3.06/1.61  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_786])).
% 3.06/1.61  tff(c_791, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_104])).
% 3.06/1.61  tff(c_794, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_791, c_12])).
% 3.06/1.61  tff(c_798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_794])).
% 3.06/1.61  tff(c_800, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_87])).
% 3.06/1.61  tff(c_821, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_800, c_12])).
% 3.06/1.61  tff(c_823, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_38])).
% 3.06/1.61  tff(c_801, plain, (![B_117, A_118]: (r2_hidden(B_117, A_118) | ~m1_subset_1(B_117, A_118) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.61  tff(c_816, plain, (![B_117]: (~m1_subset_1(B_117, '#skF_5') | ~m1_subset_1(B_117, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_801, c_36])).
% 3.06/1.61  tff(c_835, plain, (![B_120]: (~m1_subset_1(B_120, '#skF_5') | ~m1_subset_1(B_120, '#skF_6'))), inference(splitLeft, [status(thm)], [c_816])).
% 3.06/1.61  tff(c_839, plain, (![B_17]: (~m1_subset_1(B_17, '#skF_6') | ~v1_xboole_0(B_17) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_835])).
% 3.06/1.61  tff(c_843, plain, (![B_121]: (~m1_subset_1(B_121, '#skF_6') | ~v1_xboole_0(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_839])).
% 3.06/1.61  tff(c_848, plain, (![B_17]: (~v1_xboole_0(B_17) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_843])).
% 3.06/1.61  tff(c_849, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_848])).
% 3.06/1.61  tff(c_805, plain, (![B_117, A_11]: (r1_tarski(B_117, A_11) | ~m1_subset_1(B_117, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_801, c_14])).
% 3.06/1.61  tff(c_866, plain, (![B_126, A_127]: (r1_tarski(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)))), inference(negUnitSimplification, [status(thm)], [c_34, c_805])).
% 3.06/1.61  tff(c_875, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_866])).
% 3.06/1.61  tff(c_945, plain, (![C_136, B_137, A_138]: (r2_hidden(C_136, B_137) | ~r2_hidden(C_136, A_138) | ~r1_tarski(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.61  tff(c_966, plain, (![A_141, B_142]: (r2_hidden('#skF_1'(A_141), B_142) | ~r1_tarski(A_141, B_142) | v1_xboole_0(A_141))), inference(resolution, [status(thm)], [c_4, c_945])).
% 3.06/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.61  tff(c_1001, plain, (![B_144, A_145]: (~v1_xboole_0(B_144) | ~r1_tarski(A_145, B_144) | v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_966, c_2])).
% 3.06/1.61  tff(c_1007, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_875, c_1001])).
% 3.06/1.61  tff(c_1017, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_1007])).
% 3.06/1.61  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_849, c_1017])).
% 3.06/1.61  tff(c_1021, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_848])).
% 3.06/1.61  tff(c_822, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_12])).
% 3.06/1.61  tff(c_1024, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1021, c_822])).
% 3.06/1.61  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_1024])).
% 3.06/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.61  
% 3.06/1.61  Inference rules
% 3.06/1.61  ----------------------
% 3.06/1.61  #Ref     : 0
% 3.06/1.61  #Sup     : 195
% 3.06/1.61  #Fact    : 0
% 3.06/1.61  #Define  : 0
% 3.06/1.61  #Split   : 8
% 3.06/1.61  #Chain   : 0
% 3.06/1.61  #Close   : 0
% 3.06/1.61  
% 3.06/1.61  Ordering : KBO
% 3.06/1.61  
% 3.06/1.61  Simplification rules
% 3.06/1.61  ----------------------
% 3.06/1.61  #Subsume      : 62
% 3.06/1.61  #Demod        : 20
% 3.06/1.61  #Tautology    : 34
% 3.06/1.61  #SimpNegUnit  : 39
% 3.06/1.61  #BackRed      : 8
% 3.06/1.61  
% 3.06/1.61  #Partial instantiations: 0
% 3.06/1.61  #Strategies tried      : 1
% 3.06/1.61  
% 3.06/1.61  Timing (in seconds)
% 3.06/1.61  ----------------------
% 3.06/1.61  Preprocessing        : 0.35
% 3.06/1.61  Parsing              : 0.16
% 3.06/1.61  CNF conversion       : 0.03
% 3.06/1.61  Main loop            : 0.42
% 3.06/1.61  Inferencing          : 0.17
% 3.06/1.61  Reduction            : 0.11
% 3.06/1.61  Demodulation         : 0.06
% 3.06/1.61  BG Simplification    : 0.02
% 3.06/1.61  Subsumption          : 0.09
% 3.06/1.61  Abstraction          : 0.02
% 3.06/1.61  MUC search           : 0.00
% 3.06/1.61  Cooper               : 0.00
% 3.06/1.61  Total                : 0.81
% 3.06/1.61  Index Insertion      : 0.00
% 3.06/1.61  Index Deletion       : 0.00
% 3.06/1.61  Index Matching       : 0.00
% 3.06/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
