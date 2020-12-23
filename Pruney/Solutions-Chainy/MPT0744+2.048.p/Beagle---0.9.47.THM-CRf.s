%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 123 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 261 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_86,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    ! [B_15,A_14] :
      ( r1_ordinal1(B_15,A_14)
      | r1_ordinal1(A_14,B_15)
      | ~ v3_ordinal1(B_15)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1851,plain,(
    ! [B_1163] :
      ( ~ v3_ordinal1(B_1163)
      | r1_ordinal1(B_1163,B_1163) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_38])).

tff(c_58,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1758,plain,(
    ! [B_1154,A_1155] :
      ( r1_ordinal1(B_1154,A_1155)
      | r1_ordinal1(A_1155,B_1154)
      | ~ v3_ordinal1(B_1154)
      | ~ v3_ordinal1(A_1155) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_20] : r2_hidden(B_20,k1_ordinal1(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_96,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1078,plain,(
    ! [B_1072,A_1073] :
      ( r2_hidden(B_1072,A_1073)
      | B_1072 = A_1073
      | r2_hidden(A_1073,B_1072)
      | ~ v3_ordinal1(B_1072)
      | ~ v3_ordinal1(A_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | r2_hidden(A_37,k1_ordinal1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_99])).

tff(c_1222,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1078,c_107])).

tff(c_1422,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1222])).

tff(c_1467,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1422])).

tff(c_54,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1471,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1467,c_54])).

tff(c_1474,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1471])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_96,c_1474])).

tff(c_1479,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1422])).

tff(c_1483,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_99])).

tff(c_1488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1483])).

tff(c_1490,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1761,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1758,c_1490])).

tff(c_1767,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1761])).

tff(c_1792,plain,(
    ! [A_1159,B_1160] :
      ( r1_tarski(A_1159,B_1160)
      | ~ r1_ordinal1(A_1159,B_1160)
      | ~ v3_ordinal1(B_1160)
      | ~ v3_ordinal1(A_1159) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1489,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1725,plain,(
    ! [B_1152,A_1153] :
      ( B_1152 = A_1153
      | r2_hidden(A_1153,B_1152)
      | ~ r2_hidden(A_1153,k1_ordinal1(B_1152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1736,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1489,c_1725])).

tff(c_1739,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1736])).

tff(c_1743,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1739,c_54])).

tff(c_1795,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1792,c_1743])).

tff(c_1820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1767,c_1795])).

tff(c_1821,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1736])).

tff(c_1825,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1490])).

tff(c_1854,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1851,c_1825])).

tff(c_1858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:27:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.86  
% 3.50/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.86  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.50/1.86  
% 3.50/1.86  %Foreground sorts:
% 3.50/1.86  
% 3.50/1.86  
% 3.50/1.86  %Background operators:
% 3.50/1.86  
% 3.50/1.86  
% 3.50/1.86  %Foreground operators:
% 3.50/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.50/1.86  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.50/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.50/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.86  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.50/1.86  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.86  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.50/1.86  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.50/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.50/1.86  
% 3.50/1.88  tff(f_101, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.50/1.88  tff(f_55, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.50/1.88  tff(f_71, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.50/1.88  tff(f_65, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.50/1.88  tff(f_86, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.50/1.88  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.50/1.88  tff(c_56, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.88  tff(c_38, plain, (![B_15, A_14]: (r1_ordinal1(B_15, A_14) | r1_ordinal1(A_14, B_15) | ~v3_ordinal1(B_15) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.88  tff(c_1851, plain, (![B_1163]: (~v3_ordinal1(B_1163) | r1_ordinal1(B_1163, B_1163))), inference(factorization, [status(thm), theory('equality')], [c_38])).
% 3.50/1.88  tff(c_58, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.88  tff(c_1758, plain, (![B_1154, A_1155]: (r1_ordinal1(B_1154, A_1155) | r1_ordinal1(A_1155, B_1154) | ~v3_ordinal1(B_1154) | ~v3_ordinal1(A_1155))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.50/1.88  tff(c_48, plain, (![B_20]: (r2_hidden(B_20, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.50/1.88  tff(c_66, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.88  tff(c_96, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_66])).
% 3.50/1.88  tff(c_44, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.50/1.88  tff(c_1078, plain, (![B_1072, A_1073]: (r2_hidden(B_1072, A_1073) | B_1072=A_1073 | r2_hidden(A_1073, B_1072) | ~v3_ordinal1(B_1072) | ~v3_ordinal1(A_1073))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.50/1.88  tff(c_100, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | r2_hidden(A_37, k1_ordinal1(B_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.50/1.88  tff(c_60, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.88  tff(c_99, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60])).
% 3.50/1.88  tff(c_107, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_100, c_99])).
% 3.50/1.88  tff(c_1222, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1078, c_107])).
% 3.50/1.88  tff(c_1422, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1222])).
% 3.50/1.88  tff(c_1467, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1422])).
% 3.50/1.88  tff(c_54, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.88  tff(c_1471, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1467, c_54])).
% 3.50/1.88  tff(c_1474, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1471])).
% 3.50/1.88  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_96, c_1474])).
% 3.50/1.88  tff(c_1479, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1422])).
% 3.50/1.88  tff(c_1483, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_99])).
% 3.50/1.88  tff(c_1488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1483])).
% 3.50/1.88  tff(c_1490, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 3.50/1.88  tff(c_1761, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1758, c_1490])).
% 3.50/1.88  tff(c_1767, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1761])).
% 3.50/1.88  tff(c_1792, plain, (![A_1159, B_1160]: (r1_tarski(A_1159, B_1160) | ~r1_ordinal1(A_1159, B_1160) | ~v3_ordinal1(B_1160) | ~v3_ordinal1(A_1159))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.50/1.88  tff(c_1489, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_66])).
% 3.50/1.88  tff(c_1725, plain, (![B_1152, A_1153]: (B_1152=A_1153 | r2_hidden(A_1153, B_1152) | ~r2_hidden(A_1153, k1_ordinal1(B_1152)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.50/1.88  tff(c_1736, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1489, c_1725])).
% 3.50/1.88  tff(c_1739, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1736])).
% 3.50/1.88  tff(c_1743, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1739, c_54])).
% 3.50/1.88  tff(c_1795, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1792, c_1743])).
% 3.50/1.88  tff(c_1820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1767, c_1795])).
% 3.50/1.88  tff(c_1821, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1736])).
% 3.50/1.88  tff(c_1825, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1490])).
% 3.50/1.88  tff(c_1854, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1851, c_1825])).
% 3.50/1.88  tff(c_1858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1854])).
% 3.50/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.88  
% 3.50/1.88  Inference rules
% 3.50/1.88  ----------------------
% 3.50/1.88  #Ref     : 0
% 3.50/1.88  #Sup     : 312
% 3.50/1.88  #Fact    : 8
% 3.50/1.88  #Define  : 0
% 3.50/1.88  #Split   : 4
% 3.50/1.88  #Chain   : 0
% 3.50/1.88  #Close   : 0
% 3.50/1.88  
% 3.50/1.88  Ordering : KBO
% 3.50/1.88  
% 3.50/1.88  Simplification rules
% 3.50/1.88  ----------------------
% 3.50/1.88  #Subsume      : 32
% 3.50/1.88  #Demod        : 37
% 3.50/1.88  #Tautology    : 28
% 3.50/1.88  #SimpNegUnit  : 0
% 3.50/1.88  #BackRed      : 8
% 3.50/1.88  
% 3.50/1.88  #Partial instantiations: 603
% 3.50/1.88  #Strategies tried      : 1
% 3.50/1.88  
% 3.50/1.88  Timing (in seconds)
% 3.50/1.88  ----------------------
% 3.50/1.88  Preprocessing        : 0.44
% 3.50/1.88  Parsing              : 0.25
% 3.50/1.88  CNF conversion       : 0.03
% 3.50/1.88  Main loop            : 0.50
% 3.50/1.88  Inferencing          : 0.20
% 3.50/1.88  Reduction            : 0.12
% 3.50/1.88  Demodulation         : 0.08
% 3.50/1.88  BG Simplification    : 0.03
% 3.50/1.88  Subsumption          : 0.12
% 3.50/1.88  Abstraction          : 0.02
% 3.50/1.88  MUC search           : 0.00
% 3.50/1.88  Cooper               : 0.00
% 3.50/1.88  Total                : 0.97
% 3.50/1.88  Index Insertion      : 0.00
% 3.50/1.88  Index Deletion       : 0.00
% 3.50/1.88  Index Matching       : 0.00
% 3.50/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
