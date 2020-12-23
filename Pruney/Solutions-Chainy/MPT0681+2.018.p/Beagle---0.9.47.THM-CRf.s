%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.47s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 122 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [A_13,C_63] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_107,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_142,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_71)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_6,B_7,A_70] :
      ( ~ r1_xboole_0(A_6,B_7)
      | r1_xboole_0(A_70,k3_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_142,c_10])).

tff(c_306,plain,(
    ! [B_97,A_98] :
      ( k9_relat_1(B_97,A_98) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_97),A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_323,plain,(
    ! [B_97,A_6,B_7] :
      ( k9_relat_1(B_97,k3_xboole_0(A_6,B_7)) = k1_xboole_0
      | ~ v1_relat_1(B_97)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_152,c_306])).

tff(c_667,plain,(
    ! [C_160,A_161,B_162] :
      ( k3_xboole_0(k9_relat_1(C_160,A_161),k9_relat_1(C_160,B_162)) = k9_relat_1(C_160,k3_xboole_0(A_161,B_162))
      | ~ v2_funct_1(C_160)
      | ~ v1_funct_1(C_160)
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2639,plain,(
    ! [C_237,A_238,B_239] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_237,A_238),k9_relat_1(C_237,B_239)),k9_relat_1(C_237,k3_xboole_0(A_238,B_239)))
      | r1_xboole_0(k9_relat_1(C_237,A_238),k9_relat_1(C_237,B_239))
      | ~ v2_funct_1(C_237)
      | ~ v1_funct_1(C_237)
      | ~ v1_relat_1(C_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_8])).

tff(c_2798,plain,(
    ! [B_97,A_6,B_7] :
      ( r2_hidden('#skF_2'(k9_relat_1(B_97,A_6),k9_relat_1(B_97,B_7)),k1_xboole_0)
      | r1_xboole_0(k9_relat_1(B_97,A_6),k9_relat_1(B_97,B_7))
      | ~ v2_funct_1(B_97)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_2639])).

tff(c_26745,plain,(
    ! [B_586,A_587,B_588] :
      ( r1_xboole_0(k9_relat_1(B_586,A_587),k9_relat_1(B_586,B_588))
      | ~ v2_funct_1(B_586)
      | ~ v1_funct_1(B_586)
      | ~ v1_relat_1(B_586)
      | ~ v1_relat_1(B_586)
      | ~ r1_xboole_0(A_587,B_588) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2798])).

tff(c_42,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26759,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26745,c_42])).

tff(c_27158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_48,c_44,c_26759])).

tff(c_27160,plain,(
    ! [A_589] : ~ r1_xboole_0(A_589,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_27164,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) != A_15 ),
    inference(resolution,[status(thm)],[c_20,c_27160])).

tff(c_27168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_27164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.47/4.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/4.00  
% 9.47/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/4.00  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.47/4.00  
% 9.47/4.00  %Foreground sorts:
% 9.47/4.00  
% 9.47/4.00  
% 9.47/4.00  %Background operators:
% 9.47/4.00  
% 9.47/4.00  
% 9.47/4.00  %Foreground operators:
% 9.47/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.47/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.47/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.47/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.47/4.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.47/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.47/4.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.47/4.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.47/4.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.47/4.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.47/4.00  tff('#skF_5', type, '#skF_5': $i).
% 9.47/4.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.47/4.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.47/4.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.47/4.00  tff('#skF_3', type, '#skF_3': $i).
% 9.47/4.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.47/4.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.47/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.47/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.47/4.00  tff('#skF_4', type, '#skF_4': $i).
% 9.47/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.47/4.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.47/4.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.47/4.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.47/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.47/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.47/4.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.47/4.00  
% 9.47/4.01  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.47/4.01  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.47/4.01  tff(f_106, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 9.47/4.01  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.47/4.01  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.47/4.01  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.47/4.01  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 9.47/4.01  tff(f_95, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 9.47/4.01  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.47/4.01  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.47/4.01  tff(c_46, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.47/4.01  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.47/4.01  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.47/4.01  tff(c_44, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.47/4.01  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.47/4.01  tff(c_103, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.47/4.01  tff(c_106, plain, (![A_13, C_63]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 9.47/4.01  tff(c_107, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_106])).
% 9.47/4.01  tff(c_142, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), B_71) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.47/4.01  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.47/4.01  tff(c_152, plain, (![A_6, B_7, A_70]: (~r1_xboole_0(A_6, B_7) | r1_xboole_0(A_70, k3_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_142, c_10])).
% 9.47/4.01  tff(c_306, plain, (![B_97, A_98]: (k9_relat_1(B_97, A_98)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_97), A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.47/4.01  tff(c_323, plain, (![B_97, A_6, B_7]: (k9_relat_1(B_97, k3_xboole_0(A_6, B_7))=k1_xboole_0 | ~v1_relat_1(B_97) | ~r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_152, c_306])).
% 9.47/4.01  tff(c_667, plain, (![C_160, A_161, B_162]: (k3_xboole_0(k9_relat_1(C_160, A_161), k9_relat_1(C_160, B_162))=k9_relat_1(C_160, k3_xboole_0(A_161, B_162)) | ~v2_funct_1(C_160) | ~v1_funct_1(C_160) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.47/4.01  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.47/4.01  tff(c_2639, plain, (![C_237, A_238, B_239]: (r2_hidden('#skF_2'(k9_relat_1(C_237, A_238), k9_relat_1(C_237, B_239)), k9_relat_1(C_237, k3_xboole_0(A_238, B_239))) | r1_xboole_0(k9_relat_1(C_237, A_238), k9_relat_1(C_237, B_239)) | ~v2_funct_1(C_237) | ~v1_funct_1(C_237) | ~v1_relat_1(C_237))), inference(superposition, [status(thm), theory('equality')], [c_667, c_8])).
% 9.47/4.01  tff(c_2798, plain, (![B_97, A_6, B_7]: (r2_hidden('#skF_2'(k9_relat_1(B_97, A_6), k9_relat_1(B_97, B_7)), k1_xboole_0) | r1_xboole_0(k9_relat_1(B_97, A_6), k9_relat_1(B_97, B_7)) | ~v2_funct_1(B_97) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_relat_1(B_97) | ~r1_xboole_0(A_6, B_7))), inference(superposition, [status(thm), theory('equality')], [c_323, c_2639])).
% 9.47/4.01  tff(c_26745, plain, (![B_586, A_587, B_588]: (r1_xboole_0(k9_relat_1(B_586, A_587), k9_relat_1(B_586, B_588)) | ~v2_funct_1(B_586) | ~v1_funct_1(B_586) | ~v1_relat_1(B_586) | ~v1_relat_1(B_586) | ~r1_xboole_0(A_587, B_588))), inference(negUnitSimplification, [status(thm)], [c_107, c_2798])).
% 9.47/4.01  tff(c_42, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.47/4.01  tff(c_26759, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_26745, c_42])).
% 9.47/4.01  tff(c_27158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_48, c_44, c_26759])).
% 9.47/4.01  tff(c_27160, plain, (![A_589]: (~r1_xboole_0(A_589, k1_xboole_0))), inference(splitRight, [status(thm)], [c_106])).
% 9.47/4.01  tff(c_27164, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(resolution, [status(thm)], [c_20, c_27160])).
% 9.47/4.01  tff(c_27168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_27164])).
% 9.47/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.47/4.01  
% 9.47/4.01  Inference rules
% 9.47/4.01  ----------------------
% 9.47/4.01  #Ref     : 0
% 9.47/4.01  #Sup     : 6478
% 9.47/4.01  #Fact    : 0
% 9.47/4.01  #Define  : 0
% 9.47/4.01  #Split   : 1
% 9.47/4.01  #Chain   : 0
% 9.47/4.01  #Close   : 0
% 9.47/4.01  
% 9.47/4.01  Ordering : KBO
% 9.47/4.01  
% 9.47/4.01  Simplification rules
% 9.47/4.01  ----------------------
% 9.47/4.01  #Subsume      : 459
% 9.47/4.01  #Demod        : 9268
% 9.47/4.01  #Tautology    : 5096
% 9.47/4.01  #SimpNegUnit  : 153
% 9.47/4.01  #BackRed      : 1
% 9.47/4.01  
% 9.47/4.01  #Partial instantiations: 0
% 9.47/4.01  #Strategies tried      : 1
% 9.47/4.01  
% 9.47/4.01  Timing (in seconds)
% 9.47/4.01  ----------------------
% 9.47/4.02  Preprocessing        : 0.34
% 9.47/4.02  Parsing              : 0.20
% 9.47/4.02  CNF conversion       : 0.02
% 9.47/4.02  Main loop            : 2.85
% 9.47/4.02  Inferencing          : 0.78
% 9.47/4.02  Reduction            : 1.44
% 9.47/4.02  Demodulation         : 1.25
% 9.47/4.02  BG Simplification    : 0.06
% 9.47/4.02  Subsumption          : 0.45
% 9.47/4.02  Abstraction          : 0.13
% 9.47/4.02  MUC search           : 0.00
% 9.47/4.02  Cooper               : 0.00
% 9.47/4.02  Total                : 3.23
% 9.47/4.02  Index Insertion      : 0.00
% 9.47/4.02  Index Deletion       : 0.00
% 9.47/4.02  Index Matching       : 0.00
% 9.47/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
