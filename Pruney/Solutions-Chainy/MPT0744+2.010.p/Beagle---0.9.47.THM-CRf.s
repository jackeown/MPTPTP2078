%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 131 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 273 expanded)
%              Number of equality atoms :    9 (  26 expanded)
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

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_44,plain,(
    ! [B_20] : r2_hidden(B_20,k1_ordinal1(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_91,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1223,plain,(
    ! [B_1039,A_1040] :
      ( r2_hidden(B_1039,A_1040)
      | B_1039 = A_1040
      | r2_hidden(A_1040,B_1039)
      | ~ v3_ordinal1(B_1039)
      | ~ v3_ordinal1(A_1040) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden(A_19,B_20)
      | r2_hidden(A_19,k1_ordinal1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_1352,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1223,c_126])).

tff(c_1553,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1352])).

tff(c_1604,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1553])).

tff(c_52,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1611,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1604,c_52])).

tff(c_1614,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1611])).

tff(c_1618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_91,c_1614])).

tff(c_1619,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1553])).

tff(c_1624,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_122])).

tff(c_1629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1624])).

tff(c_1631,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2015,plain,(
    ! [B_1126,A_1127] :
      ( r2_hidden(B_1126,A_1127)
      | r1_ordinal1(A_1127,B_1126)
      | ~ v3_ordinal1(B_1126)
      | ~ v3_ordinal1(A_1127) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1630,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1900,plain,(
    ! [B_1114,A_1115] :
      ( B_1114 = A_1115
      | r2_hidden(A_1115,B_1114)
      | ~ r2_hidden(A_1115,k1_ordinal1(B_1114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1911,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1630,c_1900])).

tff(c_1914,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1911])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1920,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1914,c_2])).

tff(c_2038,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2015,c_1920])).

tff(c_2116,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2038])).

tff(c_2118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_2116])).

tff(c_2119,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1911])).

tff(c_2124,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_1631])).

tff(c_2133,plain,(
    ! [B_1128,A_1129] :
      ( r2_hidden(B_1128,A_1129)
      | r1_ordinal1(A_1129,B_1128)
      | ~ v3_ordinal1(B_1128)
      | ~ v3_ordinal1(A_1129) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2120,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1911])).

tff(c_2132,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_2120])).

tff(c_2136,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2133,c_2132])).

tff(c_2206,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2136])).

tff(c_2208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2124,c_2206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.60  
% 3.68/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.60  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.68/1.60  
% 3.68/1.60  %Foreground sorts:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Background operators:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Foreground operators:
% 3.68/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.68/1.60  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.68/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.68/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.60  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.68/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.68/1.60  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.68/1.60  
% 3.68/1.61  tff(f_70, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.68/1.61  tff(f_109, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.68/1.61  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.68/1.61  tff(f_85, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.68/1.61  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.68/1.61  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.68/1.61  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.68/1.61  tff(c_44, plain, (![B_20]: (r2_hidden(B_20, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.61  tff(c_56, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.68/1.61  tff(c_54, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.68/1.61  tff(c_64, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.68/1.61  tff(c_91, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_64])).
% 3.68/1.61  tff(c_40, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.61  tff(c_1223, plain, (![B_1039, A_1040]: (r2_hidden(B_1039, A_1040) | B_1039=A_1040 | r2_hidden(A_1040, B_1039) | ~v3_ordinal1(B_1039) | ~v3_ordinal1(A_1040))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.68/1.61  tff(c_46, plain, (![A_19, B_20]: (~r2_hidden(A_19, B_20) | r2_hidden(A_19, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.61  tff(c_58, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.68/1.61  tff(c_122, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58])).
% 3.68/1.61  tff(c_126, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_122])).
% 3.68/1.61  tff(c_1352, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1223, c_126])).
% 3.68/1.61  tff(c_1553, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1352])).
% 3.68/1.61  tff(c_1604, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1553])).
% 3.68/1.61  tff(c_52, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.68/1.61  tff(c_1611, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1604, c_52])).
% 3.68/1.61  tff(c_1614, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1611])).
% 3.68/1.61  tff(c_1618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_91, c_1614])).
% 3.68/1.61  tff(c_1619, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1553])).
% 3.68/1.61  tff(c_1624, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_122])).
% 3.68/1.61  tff(c_1629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1624])).
% 3.68/1.61  tff(c_1631, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 3.68/1.61  tff(c_2015, plain, (![B_1126, A_1127]: (r2_hidden(B_1126, A_1127) | r1_ordinal1(A_1127, B_1126) | ~v3_ordinal1(B_1126) | ~v3_ordinal1(A_1127))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.61  tff(c_1630, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_64])).
% 3.68/1.61  tff(c_1900, plain, (![B_1114, A_1115]: (B_1114=A_1115 | r2_hidden(A_1115, B_1114) | ~r2_hidden(A_1115, k1_ordinal1(B_1114)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.61  tff(c_1911, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1630, c_1900])).
% 3.68/1.61  tff(c_1914, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1911])).
% 3.68/1.61  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.68/1.61  tff(c_1920, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1914, c_2])).
% 3.68/1.61  tff(c_2038, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_2015, c_1920])).
% 3.68/1.61  tff(c_2116, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2038])).
% 3.68/1.61  tff(c_2118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1631, c_2116])).
% 3.68/1.61  tff(c_2119, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1911])).
% 3.68/1.61  tff(c_2124, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2119, c_1631])).
% 3.68/1.61  tff(c_2133, plain, (![B_1128, A_1129]: (r2_hidden(B_1128, A_1129) | r1_ordinal1(A_1129, B_1128) | ~v3_ordinal1(B_1128) | ~v3_ordinal1(A_1129))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.61  tff(c_2120, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1911])).
% 3.68/1.61  tff(c_2132, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2119, c_2120])).
% 3.68/1.61  tff(c_2136, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_2133, c_2132])).
% 3.68/1.61  tff(c_2206, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2136])).
% 3.68/1.61  tff(c_2208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2124, c_2206])).
% 3.68/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.61  
% 3.68/1.61  Inference rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Ref     : 0
% 3.68/1.61  #Sup     : 412
% 3.68/1.61  #Fact    : 4
% 3.68/1.61  #Define  : 0
% 3.68/1.61  #Split   : 5
% 3.68/1.61  #Chain   : 0
% 3.68/1.61  #Close   : 0
% 3.68/1.61  
% 3.68/1.61  Ordering : KBO
% 3.68/1.61  
% 3.68/1.61  Simplification rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Subsume      : 41
% 3.68/1.61  #Demod        : 34
% 3.68/1.61  #Tautology    : 29
% 3.68/1.61  #SimpNegUnit  : 2
% 3.68/1.61  #BackRed      : 10
% 3.68/1.61  
% 3.68/1.61  #Partial instantiations: 594
% 3.68/1.61  #Strategies tried      : 1
% 3.68/1.61  
% 3.68/1.61  Timing (in seconds)
% 3.68/1.61  ----------------------
% 3.68/1.61  Preprocessing        : 0.30
% 3.68/1.61  Parsing              : 0.16
% 3.68/1.61  CNF conversion       : 0.02
% 3.68/1.61  Main loop            : 0.57
% 3.68/1.61  Inferencing          : 0.22
% 3.68/1.61  Reduction            : 0.13
% 3.68/1.61  Demodulation         : 0.09
% 3.68/1.61  BG Simplification    : 0.03
% 3.68/1.61  Subsumption          : 0.14
% 3.68/1.61  Abstraction          : 0.03
% 3.68/1.61  MUC search           : 0.00
% 3.68/1.61  Cooper               : 0.00
% 3.68/1.61  Total                : 0.90
% 3.68/1.61  Index Insertion      : 0.00
% 3.68/1.61  Index Deletion       : 0.00
% 3.68/1.61  Index Matching       : 0.00
% 3.68/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
