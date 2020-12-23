%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:23 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 192 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_102,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_93,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_210,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_225,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_210])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) = k1_xboole_0
      | k1_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_30])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_310,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_1'(A_105,B_106),B_106)
      | r2_hidden('#skF_2'(A_105,B_106),A_105)
      | B_106 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_334,plain,(
    ! [B_107] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_107),B_107)
      | k1_xboole_0 = B_107 ) ),
    inference(resolution,[status(thm)],[c_310,c_76])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    ! [A_80,B_9,A_8] :
      ( m1_subset_1(A_80,B_9)
      | ~ r2_hidden(A_80,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_345,plain,(
    ! [B_107,B_9] :
      ( m1_subset_1('#skF_1'(k1_xboole_0,B_107),B_9)
      | ~ r1_tarski(B_107,B_9)
      | k1_xboole_0 = B_107 ) ),
    inference(resolution,[status(thm)],[c_334,c_231])).

tff(c_333,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_106),B_106)
      | k1_xboole_0 = B_106 ) ),
    inference(resolution,[status(thm)],[c_310,c_76])).

tff(c_415,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_435,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_415])).

tff(c_42,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_441,plain,(
    ! [D_119] :
      ( ~ r2_hidden(D_119,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_119,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_42])).

tff(c_445,plain,
    ( ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_333,c_441])).

tff(c_456,plain,(
    ~ m1_subset_1('#skF_1'(k1_xboole_0,k1_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_445])).

tff(c_461,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_345,c_456])).

tff(c_464,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_461])).

tff(c_469,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_464])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_225,c_469])).

tff(c_474,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_729,plain,(
    ! [A_170,B_171,C_172] :
      ( k2_relset_1(A_170,B_171,C_172) = k2_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_736,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_729])).

tff(c_745,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_736])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.41  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.63/1.41  
% 2.63/1.41  %Foreground sorts:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Background operators:
% 2.63/1.41  
% 2.63/1.41  
% 2.63/1.41  %Foreground operators:
% 2.63/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.63/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.63/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.63/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.41  
% 2.63/1.42  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.63/1.42  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.63/1.42  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.63/1.42  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.63/1.42  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.63/1.42  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.63/1.42  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.63/1.42  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.63/1.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.63/1.42  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.63/1.42  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.63/1.42  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.63/1.42  tff(c_44, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.63/1.42  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.63/1.42  tff(c_93, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.42  tff(c_106, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_93])).
% 2.63/1.42  tff(c_210, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.42  tff(c_225, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_210])).
% 2.63/1.42  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.42  tff(c_30, plain, (![A_15]: (k2_relat_1(A_15)=k1_xboole_0 | k1_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.42  tff(c_114, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_30])).
% 2.63/1.42  tff(c_123, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 2.63/1.42  tff(c_310, plain, (![A_105, B_106]: (r2_hidden('#skF_1'(A_105, B_106), B_106) | r2_hidden('#skF_2'(A_105, B_106), A_105) | B_106=A_105)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.42  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.42  tff(c_73, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.43  tff(c_76, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_73])).
% 2.63/1.43  tff(c_334, plain, (![B_107]: (r2_hidden('#skF_1'(k1_xboole_0, B_107), B_107) | k1_xboole_0=B_107)), inference(resolution, [status(thm)], [c_310, c_76])).
% 2.63/1.43  tff(c_20, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.43  tff(c_226, plain, (![A_80, C_81, B_82]: (m1_subset_1(A_80, C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.43  tff(c_231, plain, (![A_80, B_9, A_8]: (m1_subset_1(A_80, B_9) | ~r2_hidden(A_80, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_20, c_226])).
% 2.63/1.43  tff(c_345, plain, (![B_107, B_9]: (m1_subset_1('#skF_1'(k1_xboole_0, B_107), B_9) | ~r1_tarski(B_107, B_9) | k1_xboole_0=B_107)), inference(resolution, [status(thm)], [c_334, c_231])).
% 2.91/1.43  tff(c_333, plain, (![B_106]: (r2_hidden('#skF_1'(k1_xboole_0, B_106), B_106) | k1_xboole_0=B_106)), inference(resolution, [status(thm)], [c_310, c_76])).
% 2.91/1.43  tff(c_415, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.91/1.43  tff(c_435, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_415])).
% 2.91/1.43  tff(c_42, plain, (![D_39]: (~r2_hidden(D_39, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.43  tff(c_441, plain, (![D_119]: (~r2_hidden(D_119, k1_relat_1('#skF_5')) | ~m1_subset_1(D_119, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_42])).
% 2.91/1.43  tff(c_445, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_333, c_441])).
% 2.91/1.43  tff(c_456, plain, (~m1_subset_1('#skF_1'(k1_xboole_0, k1_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_123, c_445])).
% 2.91/1.43  tff(c_461, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_345, c_456])).
% 2.91/1.43  tff(c_464, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_123, c_461])).
% 2.91/1.43  tff(c_469, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_464])).
% 2.91/1.43  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_225, c_469])).
% 2.91/1.43  tff(c_474, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 2.91/1.43  tff(c_729, plain, (![A_170, B_171, C_172]: (k2_relset_1(A_170, B_171, C_172)=k2_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.91/1.43  tff(c_736, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_729])).
% 2.91/1.43  tff(c_745, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_474, c_736])).
% 2.91/1.43  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_745])).
% 2.91/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  Inference rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Ref     : 0
% 2.91/1.43  #Sup     : 156
% 2.91/1.43  #Fact    : 0
% 2.91/1.43  #Define  : 0
% 2.91/1.43  #Split   : 3
% 2.91/1.43  #Chain   : 0
% 2.91/1.43  #Close   : 0
% 2.91/1.43  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 32
% 2.91/1.43  #Demod        : 23
% 2.91/1.43  #Tautology    : 32
% 2.91/1.43  #SimpNegUnit  : 5
% 2.91/1.43  #BackRed      : 3
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.43  Preprocessing        : 0.32
% 2.91/1.43  Parsing              : 0.17
% 2.91/1.43  CNF conversion       : 0.02
% 2.91/1.43  Main loop            : 0.33
% 2.91/1.43  Inferencing          : 0.13
% 2.91/1.43  Reduction            : 0.09
% 2.91/1.43  Demodulation         : 0.06
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.05
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.69
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
