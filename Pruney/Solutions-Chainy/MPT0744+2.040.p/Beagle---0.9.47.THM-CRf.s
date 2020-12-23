%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 139 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 271 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_115,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_124,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_114,plain,(
    ! [B_60] : r2_hidden(B_60,k1_ordinal1(B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_122,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_120,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_130,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_152,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_334,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | r1_ordinal1(A_107,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_116,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,B_60)
      | r2_hidden(A_59,k1_ordinal1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_124,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_124])).

tff(c_208,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_116,c_204])).

tff(c_348,plain,
    ( r1_ordinal1('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_334,c_208])).

tff(c_357,plain,(
    r1_ordinal1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_122,c_348])).

tff(c_110,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ r1_ordinal1(A_57,B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_321,plain,(
    ! [A_104,B_105] :
      ( r1_tarski(A_104,B_105)
      | ~ r1_ordinal1(A_104,B_105)
      | ~ v3_ordinal1(B_105)
      | ~ v3_ordinal1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_689,plain,(
    ! [B_210,A_211] :
      ( B_210 = A_211
      | ~ r1_tarski(B_210,A_211)
      | ~ r1_ordinal1(A_211,B_210)
      | ~ v3_ordinal1(B_210)
      | ~ v3_ordinal1(A_211) ) ),
    inference(resolution,[status(thm)],[c_321,c_20])).

tff(c_748,plain,(
    ! [B_218,A_219] :
      ( B_218 = A_219
      | ~ r1_ordinal1(B_218,A_219)
      | ~ r1_ordinal1(A_219,B_218)
      | ~ v3_ordinal1(B_218)
      | ~ v3_ordinal1(A_219) ) ),
    inference(resolution,[status(thm)],[c_110,c_689])).

tff(c_752,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_357,c_748])).

tff(c_760,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_152,c_752])).

tff(c_769,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_204])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_769])).

tff(c_778,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_143,plain,(
    ! [A_68] :
      ( v1_ordinal1(A_68)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_150,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_120,c_143])).

tff(c_777,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_779,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_779])).

tff(c_783,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_918,plain,(
    ! [B_249,A_250] :
      ( B_249 = A_250
      | r2_hidden(A_250,B_249)
      | ~ r2_hidden(A_250,k1_ordinal1(B_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_934,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_783,c_918])).

tff(c_937,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_934])).

tff(c_102,plain,(
    ! [B_56,A_53] :
      ( r1_tarski(B_56,A_53)
      | ~ r2_hidden(B_56,A_53)
      | ~ v1_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_940,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_937,c_102])).

tff(c_943,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_940])).

tff(c_972,plain,(
    ! [A_254,B_255] :
      ( r1_ordinal1(A_254,B_255)
      | ~ r1_tarski(A_254,B_255)
      | ~ v3_ordinal1(B_255)
      | ~ v3_ordinal1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_978,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_943,c_972])).

tff(c_988,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_978])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_778,c_988])).

tff(c_991,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_995,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_778])).

tff(c_1017,plain,(
    ! [B_257,A_258] :
      ( r2_hidden(B_257,A_258)
      | r1_ordinal1(A_258,B_257)
      | ~ v3_ordinal1(B_257)
      | ~ v3_ordinal1(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_992,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_1007,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_992])).

tff(c_1020,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1017,c_1007])).

tff(c_1034,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1020])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_995,c_1034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.53  
% 3.41/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.53  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4
% 3.41/1.53  
% 3.41/1.53  %Foreground sorts:
% 3.41/1.53  
% 3.41/1.53  
% 3.41/1.53  %Background operators:
% 3.41/1.53  
% 3.41/1.53  
% 3.41/1.53  %Foreground operators:
% 3.41/1.53  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.41/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.41/1.53  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.53  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.41/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.53  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.41/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.41/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.41/1.53  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.41/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.53  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 3.41/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.41/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.53  
% 3.70/1.54  tff(f_115, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.70/1.54  tff(f_134, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.70/1.54  tff(f_124, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.70/1.54  tff(f_109, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.70/1.54  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.54  tff(f_92, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 3.70/1.54  tff(f_101, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 3.70/1.54  tff(c_114, plain, (![B_60]: (r2_hidden(B_60, k1_ordinal1(B_60)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.70/1.54  tff(c_122, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.70/1.54  tff(c_120, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.70/1.54  tff(c_130, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.70/1.54  tff(c_152, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_130])).
% 3.70/1.54  tff(c_334, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | r1_ordinal1(A_107, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.70/1.54  tff(c_116, plain, (![A_59, B_60]: (~r2_hidden(A_59, B_60) | r2_hidden(A_59, k1_ordinal1(B_60)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.70/1.54  tff(c_124, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.70/1.54  tff(c_204, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_124])).
% 3.70/1.54  tff(c_208, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_116, c_204])).
% 3.70/1.54  tff(c_348, plain, (r1_ordinal1('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_334, c_208])).
% 3.70/1.54  tff(c_357, plain, (r1_ordinal1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_122, c_348])).
% 3.70/1.54  tff(c_110, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~r1_ordinal1(A_57, B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.54  tff(c_321, plain, (![A_104, B_105]: (r1_tarski(A_104, B_105) | ~r1_ordinal1(A_104, B_105) | ~v3_ordinal1(B_105) | ~v3_ordinal1(A_104))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.54  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.70/1.54  tff(c_689, plain, (![B_210, A_211]: (B_210=A_211 | ~r1_tarski(B_210, A_211) | ~r1_ordinal1(A_211, B_210) | ~v3_ordinal1(B_210) | ~v3_ordinal1(A_211))), inference(resolution, [status(thm)], [c_321, c_20])).
% 3.70/1.54  tff(c_748, plain, (![B_218, A_219]: (B_218=A_219 | ~r1_ordinal1(B_218, A_219) | ~r1_ordinal1(A_219, B_218) | ~v3_ordinal1(B_218) | ~v3_ordinal1(A_219))), inference(resolution, [status(thm)], [c_110, c_689])).
% 3.70/1.54  tff(c_752, plain, ('#skF_7'='#skF_6' | ~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_357, c_748])).
% 3.70/1.54  tff(c_760, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_120, c_152, c_752])).
% 3.70/1.54  tff(c_769, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_204])).
% 3.70/1.54  tff(c_776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_769])).
% 3.70/1.54  tff(c_778, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_130])).
% 3.70/1.54  tff(c_143, plain, (![A_68]: (v1_ordinal1(A_68) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.70/1.54  tff(c_150, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_120, c_143])).
% 3.70/1.54  tff(c_777, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_130])).
% 3.70/1.54  tff(c_779, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_124])).
% 3.70/1.54  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_779])).
% 3.70/1.54  tff(c_783, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_124])).
% 3.70/1.54  tff(c_918, plain, (![B_249, A_250]: (B_249=A_250 | r2_hidden(A_250, B_249) | ~r2_hidden(A_250, k1_ordinal1(B_249)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.70/1.54  tff(c_934, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_783, c_918])).
% 3.70/1.54  tff(c_937, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_934])).
% 3.70/1.54  tff(c_102, plain, (![B_56, A_53]: (r1_tarski(B_56, A_53) | ~r2_hidden(B_56, A_53) | ~v1_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.70/1.54  tff(c_940, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_937, c_102])).
% 3.70/1.54  tff(c_943, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_940])).
% 3.70/1.54  tff(c_972, plain, (![A_254, B_255]: (r1_ordinal1(A_254, B_255) | ~r1_tarski(A_254, B_255) | ~v3_ordinal1(B_255) | ~v3_ordinal1(A_254))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.54  tff(c_978, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_943, c_972])).
% 3.70/1.54  tff(c_988, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_120, c_978])).
% 3.70/1.54  tff(c_990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_778, c_988])).
% 3.70/1.54  tff(c_991, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_934])).
% 3.70/1.54  tff(c_995, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_991, c_778])).
% 3.70/1.54  tff(c_1017, plain, (![B_257, A_258]: (r2_hidden(B_257, A_258) | r1_ordinal1(A_258, B_257) | ~v3_ordinal1(B_257) | ~v3_ordinal1(A_258))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.70/1.54  tff(c_992, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_934])).
% 3.70/1.54  tff(c_1007, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_991, c_992])).
% 3.70/1.54  tff(c_1020, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_1017, c_1007])).
% 3.70/1.54  tff(c_1034, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1020])).
% 3.70/1.54  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_995, c_1034])).
% 3.70/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.54  
% 3.70/1.54  Inference rules
% 3.70/1.54  ----------------------
% 3.70/1.54  #Ref     : 0
% 3.70/1.54  #Sup     : 190
% 3.70/1.54  #Fact    : 0
% 3.70/1.54  #Define  : 0
% 3.70/1.54  #Split   : 6
% 3.70/1.54  #Chain   : 0
% 3.70/1.54  #Close   : 0
% 3.70/1.54  
% 3.70/1.54  Ordering : KBO
% 3.70/1.54  
% 3.70/1.54  Simplification rules
% 3.70/1.54  ----------------------
% 3.70/1.54  #Subsume      : 15
% 3.70/1.54  #Demod        : 50
% 3.70/1.54  #Tautology    : 64
% 3.70/1.54  #SimpNegUnit  : 2
% 3.70/1.54  #BackRed      : 14
% 3.70/1.54  
% 3.70/1.54  #Partial instantiations: 0
% 3.70/1.54  #Strategies tried      : 1
% 3.70/1.54  
% 3.70/1.54  Timing (in seconds)
% 3.70/1.54  ----------------------
% 3.70/1.55  Preprocessing        : 0.37
% 3.70/1.55  Parsing              : 0.17
% 3.70/1.55  CNF conversion       : 0.03
% 3.70/1.55  Main loop            : 0.41
% 3.70/1.55  Inferencing          : 0.13
% 3.70/1.55  Reduction            : 0.12
% 3.70/1.55  Demodulation         : 0.08
% 3.70/1.55  BG Simplification    : 0.03
% 3.70/1.55  Subsumption          : 0.11
% 3.70/1.55  Abstraction          : 0.03
% 3.70/1.55  MUC search           : 0.00
% 3.70/1.55  Cooper               : 0.00
% 3.70/1.55  Total                : 0.81
% 3.70/1.55  Index Insertion      : 0.00
% 3.70/1.55  Index Deletion       : 0.00
% 3.70/1.55  Index Matching       : 0.00
% 3.70/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
