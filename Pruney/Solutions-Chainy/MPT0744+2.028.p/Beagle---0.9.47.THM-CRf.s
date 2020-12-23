%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 247 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_44,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_setfam_1(A),k3_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_81,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
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
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_21] : k1_setfam_1(k1_tarski(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    ! [A_42] : r1_tarski(k1_setfam_1(A_42),k3_tarski(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_21] : r1_tarski(A_21,k3_tarski(k1_tarski(A_21))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_89,plain,(
    ! [A_21] : r1_tarski(A_21,A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_1160,plain,(
    ! [A_173,B_174] :
      ( r1_ordinal1(A_173,B_174)
      | ~ r1_tarski(A_173,B_174)
      | ~ v3_ordinal1(B_174)
      | ~ v3_ordinal1(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1181,plain,(
    ! [A_175] :
      ( r1_ordinal1(A_175,A_175)
      | ~ v3_ordinal1(A_175) ) ),
    inference(resolution,[status(thm)],[c_89,c_1160])).

tff(c_32,plain,(
    ! [B_28] : r2_hidden(B_28,k1_ordinal1(B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_139,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_52])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_457,plain,(
    ! [B_99,A_100] :
      ( r2_hidden(B_99,A_100)
      | B_99 = A_100
      | r2_hidden(A_100,B_99)
      | ~ v3_ordinal1(B_99)
      | ~ v3_ordinal1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(B_36,A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_663,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(B_106,A_107)
      | r2_hidden(B_106,A_107)
      | B_106 = A_107
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(resolution,[status(thm)],[c_457,c_40])).

tff(c_140,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | r2_hidden(A_54,k1_ordinal1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_93])).

tff(c_719,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_663,c_156])).

tff(c_748,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_719])).

tff(c_764,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_767,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_764])).

tff(c_771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_139,c_767])).

tff(c_772,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_778,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_93])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_778])).

tff(c_783,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1005,plain,(
    ! [B_151,A_152] :
      ( r2_hidden(B_151,A_152)
      | r1_ordinal1(A_152,B_151)
      | ~ v3_ordinal1(B_151)
      | ~ v3_ordinal1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_784,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_876,plain,(
    ! [B_129,A_130] :
      ( B_129 = A_130
      | r2_hidden(A_130,B_129)
      | ~ r2_hidden(A_130,k1_ordinal1(B_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_887,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_784,c_876])).

tff(c_890,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_896,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_890,c_2])).

tff(c_1023,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1005,c_896])).

tff(c_1054,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1023])).

tff(c_1056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_783,c_1054])).

tff(c_1057,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_1062,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_783])).

tff(c_1184,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1181,c_1062])).

tff(c_1188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_1
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.15/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.15/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.49  
% 3.15/1.50  tff(f_105, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.15/1.50  tff(f_44, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.15/1.50  tff(f_46, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.15/1.50  tff(f_48, axiom, (![A]: r1_tarski(k1_setfam_1(A), k3_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_setfam_1)).
% 3.15/1.50  tff(f_58, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.15/1.50  tff(f_66, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.15/1.50  tff(f_81, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.15/1.50  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.15/1.50  tff(f_90, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.15/1.50  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.15/1.50  tff(c_44, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.50  tff(c_16, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.50  tff(c_18, plain, (![A_21]: (k1_setfam_1(k1_tarski(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.50  tff(c_82, plain, (![A_42]: (r1_tarski(k1_setfam_1(A_42), k3_tarski(A_42)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.50  tff(c_85, plain, (![A_21]: (r1_tarski(A_21, k3_tarski(k1_tarski(A_21))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_82])).
% 3.15/1.50  tff(c_89, plain, (![A_21]: (r1_tarski(A_21, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 3.15/1.50  tff(c_1160, plain, (![A_173, B_174]: (r1_ordinal1(A_173, B_174) | ~r1_tarski(A_173, B_174) | ~v3_ordinal1(B_174) | ~v3_ordinal1(A_173))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.50  tff(c_1181, plain, (![A_175]: (r1_ordinal1(A_175, A_175) | ~v3_ordinal1(A_175))), inference(resolution, [status(thm)], [c_89, c_1160])).
% 3.15/1.50  tff(c_32, plain, (![B_28]: (r2_hidden(B_28, k1_ordinal1(B_28)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.50  tff(c_42, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.50  tff(c_46, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.50  tff(c_93, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.15/1.50  tff(c_52, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.50  tff(c_139, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_93, c_52])).
% 3.15/1.50  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~r1_ordinal1(A_24, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.50  tff(c_457, plain, (![B_99, A_100]: (r2_hidden(B_99, A_100) | B_99=A_100 | r2_hidden(A_100, B_99) | ~v3_ordinal1(B_99) | ~v3_ordinal1(A_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.50  tff(c_40, plain, (![B_36, A_35]: (~r1_tarski(B_36, A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.15/1.50  tff(c_663, plain, (![B_106, A_107]: (~r1_tarski(B_106, A_107) | r2_hidden(B_106, A_107) | B_106=A_107 | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(resolution, [status(thm)], [c_457, c_40])).
% 3.15/1.50  tff(c_140, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | r2_hidden(A_54, k1_ordinal1(B_55)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.50  tff(c_156, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_140, c_93])).
% 3.15/1.50  tff(c_719, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_663, c_156])).
% 3.15/1.50  tff(c_748, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_719])).
% 3.15/1.50  tff(c_764, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_748])).
% 3.15/1.50  tff(c_767, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_764])).
% 3.15/1.50  tff(c_771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_139, c_767])).
% 3.15/1.50  tff(c_772, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_748])).
% 3.15/1.50  tff(c_778, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_93])).
% 3.15/1.50  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_778])).
% 3.15/1.50  tff(c_783, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.15/1.50  tff(c_1005, plain, (![B_151, A_152]: (r2_hidden(B_151, A_152) | r1_ordinal1(A_152, B_151) | ~v3_ordinal1(B_151) | ~v3_ordinal1(A_152))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.50  tff(c_784, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 3.15/1.50  tff(c_876, plain, (![B_129, A_130]: (B_129=A_130 | r2_hidden(A_130, B_129) | ~r2_hidden(A_130, k1_ordinal1(B_129)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.50  tff(c_887, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_784, c_876])).
% 3.15/1.50  tff(c_890, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_887])).
% 3.15/1.50  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.50  tff(c_896, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_890, c_2])).
% 3.15/1.50  tff(c_1023, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_1005, c_896])).
% 3.15/1.50  tff(c_1054, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1023])).
% 3.15/1.50  tff(c_1056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_783, c_1054])).
% 3.15/1.50  tff(c_1057, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_887])).
% 3.15/1.50  tff(c_1062, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_783])).
% 3.15/1.50  tff(c_1184, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_1181, c_1062])).
% 3.15/1.50  tff(c_1188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1184])).
% 3.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  Inference rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Ref     : 0
% 3.15/1.50  #Sup     : 222
% 3.15/1.50  #Fact    : 4
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 6
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 33
% 3.15/1.50  #Demod        : 64
% 3.15/1.50  #Tautology    : 60
% 3.15/1.50  #SimpNegUnit  : 3
% 3.15/1.50  #BackRed      : 11
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.15/1.51  Preprocessing        : 0.33
% 3.15/1.51  Parsing              : 0.17
% 3.15/1.51  CNF conversion       : 0.02
% 3.15/1.51  Main loop            : 0.41
% 3.15/1.51  Inferencing          : 0.15
% 3.15/1.51  Reduction            : 0.12
% 3.15/1.51  Demodulation         : 0.08
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.08
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.77
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
