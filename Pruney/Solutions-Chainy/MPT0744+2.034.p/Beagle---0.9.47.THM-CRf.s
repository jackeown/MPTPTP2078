%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 123 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 270 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_90,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_40,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( r1_ordinal1(B_9,A_8)
      | r1_ordinal1(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1529,plain,(
    ! [B_194] :
      ( ~ v3_ordinal1(B_194)
      | r1_ordinal1(B_194,B_194) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_24])).

tff(c_50,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1364,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(A_175,B_176)
      | ~ r1_ordinal1(A_175,B_176)
      | ~ v3_ordinal1(B_176)
      | ~ v3_ordinal1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_79,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ r1_ordinal1(A_11,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_25] :
      ( v3_ordinal1(k1_ordinal1(A_25))
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    ! [A_29] :
      ( v1_ordinal1(A_29)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_36,plain,(
    ! [B_15] : r2_hidden(B_15,k1_ordinal1(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_283,plain,(
    ! [A_90,C_91,B_92] :
      ( r2_hidden(A_90,C_91)
      | ~ r2_hidden(B_92,C_91)
      | ~ r1_tarski(A_90,B_92)
      | ~ v3_ordinal1(C_91)
      | ~ v3_ordinal1(B_92)
      | ~ v1_ordinal1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_933,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(A_136,k1_ordinal1(B_137))
      | ~ r1_tarski(A_136,B_137)
      | ~ v3_ordinal1(k1_ordinal1(B_137))
      | ~ v3_ordinal1(B_137)
      | ~ v1_ordinal1(A_136) ) ),
    inference(resolution,[status(thm)],[c_36,c_283])).

tff(c_52,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52])).

tff(c_1000,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_933,c_107])).

tff(c_1024,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48,c_1000])).

tff(c_1026,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1024])).

tff(c_1208,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1026])).

tff(c_1212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1208])).

tff(c_1213,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1024])).

tff(c_1233,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1213])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_79,c_1233])).

tff(c_1238,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1339,plain,(
    ! [B_173,A_174] :
      ( B_173 = A_174
      | r2_hidden(A_174,B_173)
      | ~ r2_hidden(A_174,k1_ordinal1(B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1350,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1238,c_1339])).

tff(c_1353,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1350])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1363,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1353,c_46])).

tff(c_1367,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1364,c_1363])).

tff(c_1389,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1367])).

tff(c_1437,plain,(
    ! [B_177,A_178] :
      ( r1_ordinal1(B_177,A_178)
      | r1_ordinal1(A_178,B_177)
      | ~ v3_ordinal1(B_177)
      | ~ v3_ordinal1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1239,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1441,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1437,c_1239])).

tff(c_1448,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_1441])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_1448])).

tff(c_1451,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1350])).

tff(c_1455,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1239])).

tff(c_1532,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1529,c_1455])).

tff(c_1536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n023.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 15:42:50 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.68  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.81/1.68  
% 3.81/1.68  %Foreground sorts:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Background operators:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Foreground operators:
% 3.81/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.81/1.68  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.81/1.68  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.81/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.68  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.81/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.81/1.68  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.81/1.68  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.68  
% 4.08/1.69  tff(f_105, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 4.08/1.69  tff(f_48, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 4.08/1.69  tff(f_58, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.08/1.69  tff(f_90, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 4.08/1.69  tff(f_40, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.08/1.69  tff(f_66, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 4.08/1.69  tff(f_80, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 4.08/1.69  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.08/1.69  tff(c_48, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.08/1.69  tff(c_24, plain, (![B_9, A_8]: (r1_ordinal1(B_9, A_8) | r1_ordinal1(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.08/1.69  tff(c_1529, plain, (![B_194]: (~v3_ordinal1(B_194) | r1_ordinal1(B_194, B_194))), inference(factorization, [status(thm), theory('equality')], [c_24])).
% 4.08/1.69  tff(c_50, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.08/1.69  tff(c_1364, plain, (![A_175, B_176]: (r1_tarski(A_175, B_176) | ~r1_ordinal1(A_175, B_176) | ~v3_ordinal1(B_176) | ~v3_ordinal1(A_175))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.08/1.69  tff(c_58, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.08/1.69  tff(c_79, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 4.08/1.69  tff(c_30, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~r1_ordinal1(A_11, B_12) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.08/1.69  tff(c_44, plain, (![A_25]: (v3_ordinal1(k1_ordinal1(A_25)) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.08/1.69  tff(c_60, plain, (![A_29]: (v1_ordinal1(A_29) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.08/1.69  tff(c_68, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_60])).
% 4.08/1.69  tff(c_36, plain, (![B_15]: (r2_hidden(B_15, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.08/1.69  tff(c_283, plain, (![A_90, C_91, B_92]: (r2_hidden(A_90, C_91) | ~r2_hidden(B_92, C_91) | ~r1_tarski(A_90, B_92) | ~v3_ordinal1(C_91) | ~v3_ordinal1(B_92) | ~v1_ordinal1(A_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.69  tff(c_933, plain, (![A_136, B_137]: (r2_hidden(A_136, k1_ordinal1(B_137)) | ~r1_tarski(A_136, B_137) | ~v3_ordinal1(k1_ordinal1(B_137)) | ~v3_ordinal1(B_137) | ~v1_ordinal1(A_136))), inference(resolution, [status(thm)], [c_36, c_283])).
% 4.08/1.69  tff(c_52, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.08/1.69  tff(c_107, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52])).
% 4.08/1.69  tff(c_1000, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_933, c_107])).
% 4.08/1.69  tff(c_1024, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48, c_1000])).
% 4.08/1.69  tff(c_1026, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1024])).
% 4.08/1.69  tff(c_1208, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1026])).
% 4.08/1.69  tff(c_1212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1208])).
% 4.08/1.69  tff(c_1213, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1024])).
% 4.08/1.69  tff(c_1233, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1213])).
% 4.08/1.69  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_79, c_1233])).
% 4.08/1.69  tff(c_1238, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 4.08/1.69  tff(c_1339, plain, (![B_173, A_174]: (B_173=A_174 | r2_hidden(A_174, B_173) | ~r2_hidden(A_174, k1_ordinal1(B_173)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.08/1.69  tff(c_1350, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1238, c_1339])).
% 4.08/1.69  tff(c_1353, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1350])).
% 4.08/1.69  tff(c_46, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.08/1.69  tff(c_1363, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1353, c_46])).
% 4.08/1.69  tff(c_1367, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1364, c_1363])).
% 4.08/1.69  tff(c_1389, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1367])).
% 4.08/1.69  tff(c_1437, plain, (![B_177, A_178]: (r1_ordinal1(B_177, A_178) | r1_ordinal1(A_178, B_177) | ~v3_ordinal1(B_177) | ~v3_ordinal1(A_178))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.08/1.69  tff(c_1239, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 4.08/1.69  tff(c_1441, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1437, c_1239])).
% 4.08/1.69  tff(c_1448, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_1441])).
% 4.08/1.69  tff(c_1450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1389, c_1448])).
% 4.08/1.69  tff(c_1451, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1350])).
% 4.08/1.69  tff(c_1455, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1239])).
% 4.08/1.69  tff(c_1532, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1529, c_1455])).
% 4.08/1.69  tff(c_1536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1532])).
% 4.08/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.69  
% 4.08/1.69  Inference rules
% 4.08/1.69  ----------------------
% 4.08/1.69  #Ref     : 0
% 4.08/1.69  #Sup     : 285
% 4.08/1.69  #Fact    : 12
% 4.08/1.69  #Define  : 0
% 4.08/1.69  #Split   : 5
% 4.08/1.69  #Chain   : 0
% 4.08/1.69  #Close   : 0
% 4.08/1.69  
% 4.08/1.69  Ordering : KBO
% 4.08/1.69  
% 4.08/1.69  Simplification rules
% 4.08/1.69  ----------------------
% 4.08/1.69  #Subsume      : 23
% 4.08/1.69  #Demod        : 38
% 4.08/1.69  #Tautology    : 35
% 4.08/1.69  #SimpNegUnit  : 1
% 4.08/1.69  #BackRed      : 6
% 4.08/1.69  
% 4.08/1.69  #Partial instantiations: 0
% 4.08/1.69  #Strategies tried      : 1
% 4.08/1.69  
% 4.08/1.69  Timing (in seconds)
% 4.08/1.69  ----------------------
% 4.08/1.69  Preprocessing        : 0.33
% 4.08/1.69  Parsing              : 0.16
% 4.08/1.69  CNF conversion       : 0.02
% 4.08/1.69  Main loop            : 0.62
% 4.08/1.69  Inferencing          : 0.24
% 4.08/1.69  Reduction            : 0.14
% 4.08/1.69  Demodulation         : 0.10
% 4.08/1.70  BG Simplification    : 0.03
% 4.08/1.70  Subsumption          : 0.17
% 4.08/1.70  Abstraction          : 0.03
% 4.08/1.70  MUC search           : 0.00
% 4.08/1.70  Cooper               : 0.00
% 4.08/1.70  Total                : 0.98
% 4.08/1.70  Index Insertion      : 0.00
% 4.08/1.70  Index Deletion       : 0.00
% 4.08/1.70  Index Matching       : 0.00
% 4.08/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
