%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 202 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 451 expanded)
%              Number of equality atoms :   14 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_93,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_89,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_80,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_40,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(c_40,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [A_24] :
      ( v2_wellord1(k1_wellord2(A_24))
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    ! [B_23,A_21] :
      ( k1_wellord1(k1_wellord2(B_23),A_21) = A_21
      | ~ r2_hidden(A_21,B_23)
      | ~ v3_ordinal1(B_23)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k1_wellord2(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_12] :
      ( k3_relat_1(k1_wellord2(A_12)) = A_12
      | ~ v1_relat_1(k1_wellord2(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ! [A_12] : k3_relat_1(k1_wellord2(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22])).

tff(c_60,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k1_wellord1(B_31,A_32),k3_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_12,A_32] :
      ( r1_tarski(k1_wellord1(k1_wellord2(A_12),A_32),A_12)
      | ~ v1_relat_1(k1_wellord2(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_65,plain,(
    ! [A_12,A_32] : r1_tarski(k1_wellord1(k1_wellord2(A_12),A_32),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_34,plain,(
    ! [B_26,A_25] :
      ( k2_wellord1(k1_wellord2(B_26),A_25) = k1_wellord2(A_25)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_182,plain,(
    ! [A_51,B_52] :
      ( ~ r4_wellord1(A_51,k2_wellord1(A_51,k1_wellord1(A_51,B_52)))
      | ~ r2_hidden(B_52,k3_relat_1(A_51))
      | ~ v2_wellord1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_189,plain,(
    ! [B_26,B_52] :
      ( ~ r4_wellord1(k1_wellord2(B_26),k1_wellord2(k1_wellord1(k1_wellord2(B_26),B_52)))
      | ~ r2_hidden(B_52,k3_relat_1(k1_wellord2(B_26)))
      | ~ v2_wellord1(k1_wellord2(B_26))
      | ~ v1_relat_1(k1_wellord2(B_26))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_26),B_52),B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_182])).

tff(c_194,plain,(
    ! [B_53,B_54] :
      ( ~ r4_wellord1(k1_wellord2(B_53),k1_wellord2(k1_wellord1(k1_wellord2(B_53),B_54)))
      | ~ r2_hidden(B_54,B_53)
      | ~ v2_wellord1(k1_wellord2(B_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_28,c_48,c_189])).

tff(c_257,plain,(
    ! [B_64,A_65] :
      ( ~ r4_wellord1(k1_wellord2(B_64),k1_wellord2(A_65))
      | ~ r2_hidden(A_65,B_64)
      | ~ v2_wellord1(k1_wellord2(B_64))
      | ~ r2_hidden(A_65,B_64)
      | ~ v3_ordinal1(B_64)
      | ~ v3_ordinal1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_194])).

tff(c_263,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_269,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_263])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,A_1)
      | B_3 = A_1
      | r2_hidden(A_1,B_3)
      | ~ v3_ordinal1(B_3)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [B_37,A_38] :
      ( r4_wellord1(B_37,A_38)
      | ~ r4_wellord1(A_38,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_81,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_78])).

tff(c_260,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_257])).

tff(c_266,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_260])).

tff(c_270,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_280,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_270])).

tff(c_291,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_280])).

tff(c_292,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_291])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_292])).

tff(c_303,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_328,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_328])).

tff(c_333,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_363,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_333])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.43/1.34  
% 2.43/1.34  %Foreground sorts:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Background operators:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Foreground operators:
% 2.43/1.34  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.43/1.34  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.43/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.34  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.43/1.34  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.43/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.34  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.34  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.34  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.43/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.34  
% 2.43/1.35  tff(f_107, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.43/1.35  tff(f_93, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.43/1.35  tff(f_89, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.43/1.35  tff(f_80, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.43/1.35  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.43/1.35  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 2.43/1.35  tff(f_97, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.43/1.35  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.43/1.35  tff(f_40, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.43/1.35  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.43/1.35  tff(c_40, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.43/1.35  tff(c_32, plain, (![A_24]: (v2_wellord1(k1_wellord2(A_24)) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.43/1.35  tff(c_42, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.43/1.35  tff(c_38, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.43/1.35  tff(c_30, plain, (![B_23, A_21]: (k1_wellord1(k1_wellord2(B_23), A_21)=A_21 | ~r2_hidden(A_21, B_23) | ~v3_ordinal1(B_23) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.43/1.35  tff(c_28, plain, (![A_20]: (v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.35  tff(c_22, plain, (![A_12]: (k3_relat_1(k1_wellord2(A_12))=A_12 | ~v1_relat_1(k1_wellord2(A_12)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.43/1.35  tff(c_48, plain, (![A_12]: (k3_relat_1(k1_wellord2(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22])).
% 2.43/1.35  tff(c_60, plain, (![B_31, A_32]: (r1_tarski(k1_wellord1(B_31, A_32), k3_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.35  tff(c_63, plain, (![A_12, A_32]: (r1_tarski(k1_wellord1(k1_wellord2(A_12), A_32), A_12) | ~v1_relat_1(k1_wellord2(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_60])).
% 2.43/1.35  tff(c_65, plain, (![A_12, A_32]: (r1_tarski(k1_wellord1(k1_wellord2(A_12), A_32), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63])).
% 2.43/1.35  tff(c_34, plain, (![B_26, A_25]: (k2_wellord1(k1_wellord2(B_26), A_25)=k1_wellord2(A_25) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.43/1.35  tff(c_182, plain, (![A_51, B_52]: (~r4_wellord1(A_51, k2_wellord1(A_51, k1_wellord1(A_51, B_52))) | ~r2_hidden(B_52, k3_relat_1(A_51)) | ~v2_wellord1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.35  tff(c_189, plain, (![B_26, B_52]: (~r4_wellord1(k1_wellord2(B_26), k1_wellord2(k1_wellord1(k1_wellord2(B_26), B_52))) | ~r2_hidden(B_52, k3_relat_1(k1_wellord2(B_26))) | ~v2_wellord1(k1_wellord2(B_26)) | ~v1_relat_1(k1_wellord2(B_26)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_26), B_52), B_26))), inference(superposition, [status(thm), theory('equality')], [c_34, c_182])).
% 2.43/1.35  tff(c_194, plain, (![B_53, B_54]: (~r4_wellord1(k1_wellord2(B_53), k1_wellord2(k1_wellord1(k1_wellord2(B_53), B_54))) | ~r2_hidden(B_54, B_53) | ~v2_wellord1(k1_wellord2(B_53)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_28, c_48, c_189])).
% 2.43/1.35  tff(c_257, plain, (![B_64, A_65]: (~r4_wellord1(k1_wellord2(B_64), k1_wellord2(A_65)) | ~r2_hidden(A_65, B_64) | ~v2_wellord1(k1_wellord2(B_64)) | ~r2_hidden(A_65, B_64) | ~v3_ordinal1(B_64) | ~v3_ordinal1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_30, c_194])).
% 2.43/1.35  tff(c_263, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_257])).
% 2.43/1.35  tff(c_269, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_263])).
% 2.43/1.35  tff(c_271, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_269])).
% 2.43/1.35  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.43/1.35  tff(c_2, plain, (![B_3, A_1]: (r2_hidden(B_3, A_1) | B_3=A_1 | r2_hidden(A_1, B_3) | ~v3_ordinal1(B_3) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.35  tff(c_76, plain, (![B_37, A_38]: (r4_wellord1(B_37, A_38) | ~r4_wellord1(A_38, B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.35  tff(c_78, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_76])).
% 2.43/1.35  tff(c_81, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_78])).
% 2.43/1.35  tff(c_260, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_81, c_257])).
% 2.43/1.35  tff(c_266, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_260])).
% 2.43/1.35  tff(c_270, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_266])).
% 2.43/1.35  tff(c_280, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_270])).
% 2.43/1.35  tff(c_291, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_280])).
% 2.43/1.35  tff(c_292, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_291])).
% 2.43/1.35  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_292])).
% 2.43/1.35  tff(c_303, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_269])).
% 2.43/1.35  tff(c_328, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_303])).
% 2.43/1.35  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_328])).
% 2.43/1.35  tff(c_333, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_266])).
% 2.43/1.35  tff(c_363, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_333])).
% 2.43/1.35  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_363])).
% 2.43/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  Inference rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Ref     : 0
% 2.43/1.35  #Sup     : 51
% 2.43/1.35  #Fact    : 4
% 2.43/1.35  #Define  : 0
% 2.43/1.35  #Split   : 2
% 2.43/1.35  #Chain   : 0
% 2.43/1.35  #Close   : 0
% 2.43/1.35  
% 2.43/1.35  Ordering : KBO
% 2.43/1.35  
% 2.43/1.35  Simplification rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Subsume      : 2
% 2.43/1.35  #Demod        : 80
% 2.43/1.35  #Tautology    : 25
% 2.43/1.35  #SimpNegUnit  : 8
% 2.43/1.35  #BackRed      : 0
% 2.43/1.35  
% 2.43/1.35  #Partial instantiations: 0
% 2.43/1.35  #Strategies tried      : 1
% 2.43/1.35  
% 2.43/1.35  Timing (in seconds)
% 2.43/1.35  ----------------------
% 2.43/1.36  Preprocessing        : 0.32
% 2.43/1.36  Parsing              : 0.16
% 2.43/1.36  CNF conversion       : 0.02
% 2.43/1.36  Main loop            : 0.23
% 2.43/1.36  Inferencing          : 0.08
% 2.43/1.36  Reduction            : 0.07
% 2.43/1.36  Demodulation         : 0.06
% 2.43/1.36  BG Simplification    : 0.02
% 2.43/1.36  Subsumption          : 0.04
% 2.43/1.36  Abstraction          : 0.01
% 2.43/1.36  MUC search           : 0.00
% 2.43/1.36  Cooper               : 0.00
% 2.43/1.36  Total                : 0.58
% 2.43/1.36  Index Insertion      : 0.00
% 2.43/1.36  Index Deletion       : 0.00
% 2.43/1.36  Index Matching       : 0.00
% 2.43/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
