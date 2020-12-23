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
% DateTime   : Thu Dec  3 10:10:31 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 109 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 279 expanded)
%              Number of equality atoms :    5 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v6_relat_2 > v3_ordinal1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v6_relat_2(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

tff(f_83,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_81,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(c_44,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_14] :
      ( k3_relat_1(k1_wellord2(A_14)) = A_14
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_14] : k3_relat_1(k1_wellord2(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_84,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),k3_relat_1(A_30))
      | v6_relat_2(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_14)),A_14)
      | v6_relat_2(k1_wellord2(A_14))
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_84])).

tff(c_94,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_31)),A_31)
      | v6_relat_2(k1_wellord2(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_90])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v3_ordinal1(A_5)
      | ~ r2_hidden(A_5,B_6)
      | ~ v3_ordinal1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_31] :
      ( v3_ordinal1('#skF_1'(k1_wellord2(A_31)))
      | ~ v3_ordinal1(A_31)
      | v6_relat_2(k1_wellord2(A_31)) ) ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_69,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_2'(A_28),k3_relat_1(A_28))
      | v6_relat_2(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_14)),A_14)
      | v6_relat_2(k1_wellord2(A_14))
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_69])).

tff(c_79,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_29)),A_29)
      | v6_relat_2(k1_wellord2(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75])).

tff(c_83,plain,(
    ! [A_29] :
      ( v3_ordinal1('#skF_2'(k1_wellord2(A_29)))
      | ~ v3_ordinal1(A_29)
      | v6_relat_2(k1_wellord2(A_29)) ) ),
    inference(resolution,[status(thm)],[c_79,c_8])).

tff(c_93,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_14)),A_14)
      | v6_relat_2(k1_wellord2(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_90])).

tff(c_78,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_14)),A_14)
      | v6_relat_2(k1_wellord2(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [C_20,D_21,A_14] :
      ( r2_hidden(k4_tarski(C_20,D_21),k1_wellord2(A_14))
      | ~ r1_tarski(C_20,D_21)
      | ~ r2_hidden(D_21,A_14)
      | ~ r2_hidden(C_20,A_14)
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_173,plain,(
    ! [C_48,D_49,A_50] :
      ( r2_hidden(k4_tarski(C_48,D_49),k1_wellord2(A_50))
      | ~ r1_tarski(C_48,D_49)
      | ~ r2_hidden(D_49,A_50)
      | ~ r2_hidden(C_48,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_7),'#skF_1'(A_7)),A_7)
      | v6_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [A_50] :
      ( v6_relat_2(k1_wellord2(A_50))
      | ~ v1_relat_1(k1_wellord2(A_50))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_50)),'#skF_1'(k1_wellord2(A_50)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_50)),A_50)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_50)),A_50) ) ),
    inference(resolution,[status(thm)],[c_173,c_12])).

tff(c_257,plain,(
    ! [A_61] :
      ( v6_relat_2(k1_wellord2(A_61))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_61)),'#skF_1'(k1_wellord2(A_61)))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_61)),A_61)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_61)),A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_181])).

tff(c_639,plain,(
    ! [A_90] :
      ( v6_relat_2(k1_wellord2(A_90))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_90)),A_90)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_90)),A_90)
      | ~ r1_ordinal1('#skF_2'(k1_wellord2(A_90)),'#skF_1'(k1_wellord2(A_90)))
      | ~ v3_ordinal1('#skF_1'(k1_wellord2(A_90)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_90))) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_670,plain,(
    ! [A_95] :
      ( v6_relat_2(k1_wellord2(A_95))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_95)),A_95)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_95)),A_95)
      | r1_ordinal1('#skF_1'(k1_wellord2(A_95)),'#skF_2'(k1_wellord2(A_95)))
      | ~ v3_ordinal1('#skF_1'(k1_wellord2(A_95)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_95))) ) ),
    inference(resolution,[status(thm)],[c_2,c_639])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_7),'#skF_2'(A_7)),A_7)
      | v6_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_177,plain,(
    ! [A_50] :
      ( v6_relat_2(k1_wellord2(A_50))
      | ~ v1_relat_1(k1_wellord2(A_50))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_50)),'#skF_2'(k1_wellord2(A_50)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_50)),A_50)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_50)),A_50) ) ),
    inference(resolution,[status(thm)],[c_173,c_14])).

tff(c_262,plain,(
    ! [A_62] :
      ( v6_relat_2(k1_wellord2(A_62))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_62)),'#skF_2'(k1_wellord2(A_62)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_62)),A_62)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_62)),A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_177])).

tff(c_266,plain,(
    ! [A_62] :
      ( v6_relat_2(k1_wellord2(A_62))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_62)),A_62)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_62)),A_62)
      | ~ r1_ordinal1('#skF_1'(k1_wellord2(A_62)),'#skF_2'(k1_wellord2(A_62)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_62)))
      | ~ v3_ordinal1('#skF_1'(k1_wellord2(A_62))) ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_675,plain,(
    ! [A_96] :
      ( v6_relat_2(k1_wellord2(A_96))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_96)),A_96)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_96)),A_96)
      | ~ v3_ordinal1('#skF_1'(k1_wellord2(A_96)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_96))) ) ),
    inference(resolution,[status(thm)],[c_670,c_266])).

tff(c_680,plain,(
    ! [A_97] :
      ( ~ r2_hidden('#skF_1'(k1_wellord2(A_97)),A_97)
      | ~ v3_ordinal1('#skF_1'(k1_wellord2(A_97)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_97)))
      | v6_relat_2(k1_wellord2(A_97)) ) ),
    inference(resolution,[status(thm)],[c_78,c_675])).

tff(c_685,plain,(
    ! [A_98] :
      ( ~ v3_ordinal1('#skF_1'(k1_wellord2(A_98)))
      | ~ v3_ordinal1('#skF_2'(k1_wellord2(A_98)))
      | v6_relat_2(k1_wellord2(A_98)) ) ),
    inference(resolution,[status(thm)],[c_93,c_680])).

tff(c_690,plain,(
    ! [A_99] :
      ( ~ v3_ordinal1('#skF_1'(k1_wellord2(A_99)))
      | ~ v3_ordinal1(A_99)
      | v6_relat_2(k1_wellord2(A_99)) ) ),
    inference(resolution,[status(thm)],[c_83,c_685])).

tff(c_738,plain,(
    ! [A_101] :
      ( ~ v3_ordinal1(A_101)
      | v6_relat_2(k1_wellord2(A_101)) ) ),
    inference(resolution,[status(thm)],[c_98,c_690])).

tff(c_42,plain,(
    ~ v6_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_747,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_738,c_42])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.84  
% 3.60/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.84  %$ r2_hidden > r1_tarski > r1_ordinal1 > v6_relat_2 > v3_ordinal1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 3.60/1.84  
% 3.60/1.84  %Foreground sorts:
% 3.60/1.84  
% 3.60/1.84  
% 3.60/1.84  %Background operators:
% 3.60/1.84  
% 3.60/1.84  
% 3.60/1.84  %Foreground operators:
% 3.60/1.84  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.60/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.60/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.60/1.84  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.60/1.84  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 3.60/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.60/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.84  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.60/1.84  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.84  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.60/1.84  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.60/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.60/1.84  
% 3.60/1.85  tff(f_88, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v6_relat_2(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_wellord2)).
% 3.60/1.85  tff(f_83, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.60/1.85  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.60/1.85  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 3.60/1.85  tff(f_47, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.60/1.85  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.60/1.85  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.60/1.85  tff(c_44, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.60/1.85  tff(c_40, plain, (![A_22]: (v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.60/1.85  tff(c_34, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14 | ~v1_relat_1(k1_wellord2(A_14)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.85  tff(c_50, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 3.60/1.85  tff(c_84, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), k3_relat_1(A_30)) | v6_relat_2(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.60/1.85  tff(c_90, plain, (![A_14]: (r2_hidden('#skF_1'(k1_wellord2(A_14)), A_14) | v6_relat_2(k1_wellord2(A_14)) | ~v1_relat_1(k1_wellord2(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_84])).
% 3.60/1.85  tff(c_94, plain, (![A_31]: (r2_hidden('#skF_1'(k1_wellord2(A_31)), A_31) | v6_relat_2(k1_wellord2(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_90])).
% 3.60/1.85  tff(c_8, plain, (![A_5, B_6]: (v3_ordinal1(A_5) | ~r2_hidden(A_5, B_6) | ~v3_ordinal1(B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.60/1.85  tff(c_98, plain, (![A_31]: (v3_ordinal1('#skF_1'(k1_wellord2(A_31))) | ~v3_ordinal1(A_31) | v6_relat_2(k1_wellord2(A_31)))), inference(resolution, [status(thm)], [c_94, c_8])).
% 3.60/1.85  tff(c_69, plain, (![A_28]: (r2_hidden('#skF_2'(A_28), k3_relat_1(A_28)) | v6_relat_2(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.60/1.85  tff(c_75, plain, (![A_14]: (r2_hidden('#skF_2'(k1_wellord2(A_14)), A_14) | v6_relat_2(k1_wellord2(A_14)) | ~v1_relat_1(k1_wellord2(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_69])).
% 3.60/1.85  tff(c_79, plain, (![A_29]: (r2_hidden('#skF_2'(k1_wellord2(A_29)), A_29) | v6_relat_2(k1_wellord2(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75])).
% 3.60/1.85  tff(c_83, plain, (![A_29]: (v3_ordinal1('#skF_2'(k1_wellord2(A_29))) | ~v3_ordinal1(A_29) | v6_relat_2(k1_wellord2(A_29)))), inference(resolution, [status(thm)], [c_79, c_8])).
% 3.60/1.85  tff(c_93, plain, (![A_14]: (r2_hidden('#skF_1'(k1_wellord2(A_14)), A_14) | v6_relat_2(k1_wellord2(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_90])).
% 3.60/1.85  tff(c_78, plain, (![A_14]: (r2_hidden('#skF_2'(k1_wellord2(A_14)), A_14) | v6_relat_2(k1_wellord2(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75])).
% 3.60/1.85  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.60/1.85  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.85  tff(c_36, plain, (![C_20, D_21, A_14]: (r2_hidden(k4_tarski(C_20, D_21), k1_wellord2(A_14)) | ~r1_tarski(C_20, D_21) | ~r2_hidden(D_21, A_14) | ~r2_hidden(C_20, A_14) | ~v1_relat_1(k1_wellord2(A_14)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.85  tff(c_173, plain, (![C_48, D_49, A_50]: (r2_hidden(k4_tarski(C_48, D_49), k1_wellord2(A_50)) | ~r1_tarski(C_48, D_49) | ~r2_hidden(D_49, A_50) | ~r2_hidden(C_48, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.60/1.85  tff(c_12, plain, (![A_7]: (~r2_hidden(k4_tarski('#skF_2'(A_7), '#skF_1'(A_7)), A_7) | v6_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.60/1.85  tff(c_181, plain, (![A_50]: (v6_relat_2(k1_wellord2(A_50)) | ~v1_relat_1(k1_wellord2(A_50)) | ~r1_tarski('#skF_2'(k1_wellord2(A_50)), '#skF_1'(k1_wellord2(A_50))) | ~r2_hidden('#skF_1'(k1_wellord2(A_50)), A_50) | ~r2_hidden('#skF_2'(k1_wellord2(A_50)), A_50))), inference(resolution, [status(thm)], [c_173, c_12])).
% 3.60/1.85  tff(c_257, plain, (![A_61]: (v6_relat_2(k1_wellord2(A_61)) | ~r1_tarski('#skF_2'(k1_wellord2(A_61)), '#skF_1'(k1_wellord2(A_61))) | ~r2_hidden('#skF_1'(k1_wellord2(A_61)), A_61) | ~r2_hidden('#skF_2'(k1_wellord2(A_61)), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_181])).
% 3.60/1.85  tff(c_639, plain, (![A_90]: (v6_relat_2(k1_wellord2(A_90)) | ~r2_hidden('#skF_1'(k1_wellord2(A_90)), A_90) | ~r2_hidden('#skF_2'(k1_wellord2(A_90)), A_90) | ~r1_ordinal1('#skF_2'(k1_wellord2(A_90)), '#skF_1'(k1_wellord2(A_90))) | ~v3_ordinal1('#skF_1'(k1_wellord2(A_90))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_90))))), inference(resolution, [status(thm)], [c_6, c_257])).
% 3.60/1.85  tff(c_670, plain, (![A_95]: (v6_relat_2(k1_wellord2(A_95)) | ~r2_hidden('#skF_1'(k1_wellord2(A_95)), A_95) | ~r2_hidden('#skF_2'(k1_wellord2(A_95)), A_95) | r1_ordinal1('#skF_1'(k1_wellord2(A_95)), '#skF_2'(k1_wellord2(A_95))) | ~v3_ordinal1('#skF_1'(k1_wellord2(A_95))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_95))))), inference(resolution, [status(thm)], [c_2, c_639])).
% 3.60/1.85  tff(c_14, plain, (![A_7]: (~r2_hidden(k4_tarski('#skF_1'(A_7), '#skF_2'(A_7)), A_7) | v6_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.60/1.85  tff(c_177, plain, (![A_50]: (v6_relat_2(k1_wellord2(A_50)) | ~v1_relat_1(k1_wellord2(A_50)) | ~r1_tarski('#skF_1'(k1_wellord2(A_50)), '#skF_2'(k1_wellord2(A_50))) | ~r2_hidden('#skF_2'(k1_wellord2(A_50)), A_50) | ~r2_hidden('#skF_1'(k1_wellord2(A_50)), A_50))), inference(resolution, [status(thm)], [c_173, c_14])).
% 3.60/1.85  tff(c_262, plain, (![A_62]: (v6_relat_2(k1_wellord2(A_62)) | ~r1_tarski('#skF_1'(k1_wellord2(A_62)), '#skF_2'(k1_wellord2(A_62))) | ~r2_hidden('#skF_2'(k1_wellord2(A_62)), A_62) | ~r2_hidden('#skF_1'(k1_wellord2(A_62)), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_177])).
% 3.60/1.85  tff(c_266, plain, (![A_62]: (v6_relat_2(k1_wellord2(A_62)) | ~r2_hidden('#skF_2'(k1_wellord2(A_62)), A_62) | ~r2_hidden('#skF_1'(k1_wellord2(A_62)), A_62) | ~r1_ordinal1('#skF_1'(k1_wellord2(A_62)), '#skF_2'(k1_wellord2(A_62))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_62))) | ~v3_ordinal1('#skF_1'(k1_wellord2(A_62))))), inference(resolution, [status(thm)], [c_6, c_262])).
% 3.60/1.85  tff(c_675, plain, (![A_96]: (v6_relat_2(k1_wellord2(A_96)) | ~r2_hidden('#skF_1'(k1_wellord2(A_96)), A_96) | ~r2_hidden('#skF_2'(k1_wellord2(A_96)), A_96) | ~v3_ordinal1('#skF_1'(k1_wellord2(A_96))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_96))))), inference(resolution, [status(thm)], [c_670, c_266])).
% 3.60/1.85  tff(c_680, plain, (![A_97]: (~r2_hidden('#skF_1'(k1_wellord2(A_97)), A_97) | ~v3_ordinal1('#skF_1'(k1_wellord2(A_97))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_97))) | v6_relat_2(k1_wellord2(A_97)))), inference(resolution, [status(thm)], [c_78, c_675])).
% 3.60/1.85  tff(c_685, plain, (![A_98]: (~v3_ordinal1('#skF_1'(k1_wellord2(A_98))) | ~v3_ordinal1('#skF_2'(k1_wellord2(A_98))) | v6_relat_2(k1_wellord2(A_98)))), inference(resolution, [status(thm)], [c_93, c_680])).
% 3.60/1.85  tff(c_690, plain, (![A_99]: (~v3_ordinal1('#skF_1'(k1_wellord2(A_99))) | ~v3_ordinal1(A_99) | v6_relat_2(k1_wellord2(A_99)))), inference(resolution, [status(thm)], [c_83, c_685])).
% 3.60/1.85  tff(c_738, plain, (![A_101]: (~v3_ordinal1(A_101) | v6_relat_2(k1_wellord2(A_101)))), inference(resolution, [status(thm)], [c_98, c_690])).
% 3.60/1.85  tff(c_42, plain, (~v6_relat_2(k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.60/1.85  tff(c_747, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_738, c_42])).
% 3.60/1.85  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_747])).
% 3.60/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.85  
% 3.60/1.85  Inference rules
% 3.60/1.85  ----------------------
% 3.60/1.85  #Ref     : 0
% 3.60/1.85  #Sup     : 149
% 3.60/1.85  #Fact    : 4
% 3.60/1.85  #Define  : 0
% 3.60/1.85  #Split   : 0
% 3.60/1.85  #Chain   : 0
% 3.60/1.85  #Close   : 0
% 3.60/1.85  
% 3.60/1.85  Ordering : KBO
% 3.60/1.85  
% 3.60/1.85  Simplification rules
% 3.60/1.85  ----------------------
% 3.60/1.85  #Subsume      : 15
% 3.60/1.85  #Demod        : 144
% 3.60/1.85  #Tautology    : 52
% 3.60/1.85  #SimpNegUnit  : 0
% 3.60/1.85  #BackRed      : 0
% 3.60/1.85  
% 3.60/1.85  #Partial instantiations: 0
% 3.60/1.85  #Strategies tried      : 1
% 3.60/1.85  
% 3.60/1.85  Timing (in seconds)
% 3.60/1.85  ----------------------
% 3.60/1.86  Preprocessing        : 0.50
% 3.60/1.86  Parsing              : 0.25
% 3.60/1.86  CNF conversion       : 0.04
% 3.60/1.86  Main loop            : 0.50
% 3.60/1.86  Inferencing          : 0.17
% 3.60/1.86  Reduction            : 0.14
% 3.60/1.86  Demodulation         : 0.11
% 3.60/1.86  BG Simplification    : 0.04
% 3.60/1.86  Subsumption          : 0.11
% 3.60/1.86  Abstraction          : 0.03
% 3.60/1.86  MUC search           : 0.00
% 3.60/1.86  Cooper               : 0.00
% 3.60/1.86  Total                : 1.04
% 3.60/1.86  Index Insertion      : 0.00
% 3.60/1.86  Index Deletion       : 0.00
% 3.60/1.86  Index Matching       : 0.00
% 3.60/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
