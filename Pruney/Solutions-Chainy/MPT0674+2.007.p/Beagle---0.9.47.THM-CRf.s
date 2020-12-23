%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:23 EST 2020

% Result     : Theorem 22.03s
% Output     : CNFRefutation 22.03s
% Verified   : 
% Statistics : Number of formulae       :   60 (  68 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 132 expanded)
%              Number of equality atoms :   41 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

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

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [A_26,B_27] : r1_tarski(k1_tarski(A_26),k2_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_55,plain,(
    ! [A_6] : r1_tarski(k1_tarski(A_6),k1_tarski(A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_58,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | ~ r1_tarski(k1_tarski(A_31),B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_6] : r2_hidden(A_6,k1_tarski(A_6)) ),
    inference(resolution,[status(thm)],[c_55,c_58])).

tff(c_92,plain,(
    ! [B_51,A_52] :
      ( r1_xboole_0(k1_relat_1(B_51),A_52)
      | k9_relat_1(B_51,A_52) != k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    ! [C_65,A_66,B_67] :
      ( ~ r2_hidden(C_65,A_66)
      | ~ r2_hidden(C_65,k1_relat_1(B_67))
      | k9_relat_1(B_67,A_66) != k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_192,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden(A_71,k1_relat_1(B_72))
      | k9_relat_1(B_72,k1_tarski(A_71)) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_68,c_146])).

tff(c_215,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_192])).

tff(c_223,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_215])).

tff(c_226,plain,
    ( k11_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_228,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_226])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),A_9)
      | k1_xboole_0 = A_9
      | k1_tarski(B_10) = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ r2_hidden(B_20,k11_relat_1(C_21,A_19))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_131,plain,(
    ! [C_62,A_63,B_64] :
      ( k1_funct_1(C_62,A_63) = B_64
      | ~ r2_hidden(k4_tarski(A_63,B_64),C_62)
      | ~ v1_funct_1(C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_260,plain,(
    ! [C_77,A_78,B_79] :
      ( k1_funct_1(C_77,A_78) = B_79
      | ~ v1_funct_1(C_77)
      | ~ r2_hidden(B_79,k11_relat_1(C_77,A_78))
      | ~ v1_relat_1(C_77) ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_1996,plain,(
    ! [C_275,A_276,B_277] :
      ( '#skF_2'(k11_relat_1(C_275,A_276),B_277) = k1_funct_1(C_275,A_276)
      | ~ v1_funct_1(C_275)
      | ~ v1_relat_1(C_275)
      | k11_relat_1(C_275,A_276) = k1_xboole_0
      | k1_tarski(B_277) = k11_relat_1(C_275,A_276) ) ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( '#skF_2'(A_9,B_10) != B_10
      | k1_xboole_0 = A_9
      | k1_tarski(B_10) = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2007,plain,(
    ! [C_275,A_276,B_277] :
      ( k1_funct_1(C_275,A_276) != B_277
      | k11_relat_1(C_275,A_276) = k1_xboole_0
      | k1_tarski(B_277) = k11_relat_1(C_275,A_276)
      | ~ v1_funct_1(C_275)
      | ~ v1_relat_1(C_275)
      | k11_relat_1(C_275,A_276) = k1_xboole_0
      | k1_tarski(B_277) = k11_relat_1(C_275,A_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_14])).

tff(c_12873,plain,(
    ! [C_275,A_276] :
      ( k11_relat_1(C_275,A_276) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_275,A_276)) = k11_relat_1(C_275,A_276)
      | ~ v1_funct_1(C_275)
      | ~ v1_relat_1(C_275)
      | k11_relat_1(C_275,A_276) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_275,A_276)) = k11_relat_1(C_275,A_276) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2007])).

tff(c_42705,plain,(
    ! [C_1722,A_1723] :
      ( ~ v1_funct_1(C_1722)
      | ~ v1_relat_1(C_1722)
      | k11_relat_1(C_1722,A_1723) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_1722,A_1723)) = k11_relat_1(C_1722,A_1723) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12873])).

tff(c_36,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42774,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42705,c_36])).

tff(c_42793,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_42774])).

tff(c_42795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_42793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.03/11.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.03/11.48  
% 22.03/11.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.03/11.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 22.03/11.49  
% 22.03/11.49  %Foreground sorts:
% 22.03/11.49  
% 22.03/11.49  
% 22.03/11.49  %Background operators:
% 22.03/11.49  
% 22.03/11.49  
% 22.03/11.49  %Foreground operators:
% 22.03/11.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.03/11.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.03/11.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.03/11.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.03/11.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.03/11.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.03/11.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.03/11.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.03/11.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 22.03/11.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.03/11.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 22.03/11.49  tff('#skF_3', type, '#skF_3': $i).
% 22.03/11.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.03/11.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.03/11.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.03/11.49  tff('#skF_4', type, '#skF_4': $i).
% 22.03/11.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.03/11.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.03/11.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.03/11.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.03/11.49  
% 22.03/11.50  tff(f_101, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 22.03/11.50  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 22.03/11.50  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 22.03/11.50  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 22.03/11.50  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 22.03/11.50  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 22.03/11.50  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 22.03/11.50  tff(f_63, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 22.03/11.50  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 22.03/11.50  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 22.03/11.50  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.03/11.50  tff(c_20, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.03/11.50  tff(c_38, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.03/11.50  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.03/11.50  tff(c_52, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.03/11.50  tff(c_55, plain, (![A_6]: (r1_tarski(k1_tarski(A_6), k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 22.03/11.50  tff(c_58, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | ~r1_tarski(k1_tarski(A_31), B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.03/11.50  tff(c_68, plain, (![A_6]: (r2_hidden(A_6, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_55, c_58])).
% 22.03/11.50  tff(c_92, plain, (![B_51, A_52]: (r1_xboole_0(k1_relat_1(B_51), A_52) | k9_relat_1(B_51, A_52)!=k1_xboole_0 | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.03/11.50  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.03/11.50  tff(c_146, plain, (![C_65, A_66, B_67]: (~r2_hidden(C_65, A_66) | ~r2_hidden(C_65, k1_relat_1(B_67)) | k9_relat_1(B_67, A_66)!=k1_xboole_0 | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_92, c_2])).
% 22.03/11.50  tff(c_192, plain, (![A_71, B_72]: (~r2_hidden(A_71, k1_relat_1(B_72)) | k9_relat_1(B_72, k1_tarski(A_71))!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_68, c_146])).
% 22.03/11.50  tff(c_215, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_192])).
% 22.03/11.50  tff(c_223, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_215])).
% 22.03/11.50  tff(c_226, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_223])).
% 22.03/11.50  tff(c_228, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_226])).
% 22.03/11.50  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.03/11.50  tff(c_16, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), A_9) | k1_xboole_0=A_9 | k1_tarski(B_10)=A_9)), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.03/11.50  tff(c_26, plain, (![A_19, B_20, C_21]: (r2_hidden(k4_tarski(A_19, B_20), C_21) | ~r2_hidden(B_20, k11_relat_1(C_21, A_19)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.03/11.50  tff(c_131, plain, (![C_62, A_63, B_64]: (k1_funct_1(C_62, A_63)=B_64 | ~r2_hidden(k4_tarski(A_63, B_64), C_62) | ~v1_funct_1(C_62) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_92])).
% 22.03/11.50  tff(c_260, plain, (![C_77, A_78, B_79]: (k1_funct_1(C_77, A_78)=B_79 | ~v1_funct_1(C_77) | ~r2_hidden(B_79, k11_relat_1(C_77, A_78)) | ~v1_relat_1(C_77))), inference(resolution, [status(thm)], [c_26, c_131])).
% 22.03/11.50  tff(c_1996, plain, (![C_275, A_276, B_277]: ('#skF_2'(k11_relat_1(C_275, A_276), B_277)=k1_funct_1(C_275, A_276) | ~v1_funct_1(C_275) | ~v1_relat_1(C_275) | k11_relat_1(C_275, A_276)=k1_xboole_0 | k1_tarski(B_277)=k11_relat_1(C_275, A_276))), inference(resolution, [status(thm)], [c_16, c_260])).
% 22.03/11.50  tff(c_14, plain, (![A_9, B_10]: ('#skF_2'(A_9, B_10)!=B_10 | k1_xboole_0=A_9 | k1_tarski(B_10)=A_9)), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.03/11.50  tff(c_2007, plain, (![C_275, A_276, B_277]: (k1_funct_1(C_275, A_276)!=B_277 | k11_relat_1(C_275, A_276)=k1_xboole_0 | k1_tarski(B_277)=k11_relat_1(C_275, A_276) | ~v1_funct_1(C_275) | ~v1_relat_1(C_275) | k11_relat_1(C_275, A_276)=k1_xboole_0 | k1_tarski(B_277)=k11_relat_1(C_275, A_276))), inference(superposition, [status(thm), theory('equality')], [c_1996, c_14])).
% 22.03/11.50  tff(c_12873, plain, (![C_275, A_276]: (k11_relat_1(C_275, A_276)=k1_xboole_0 | k1_tarski(k1_funct_1(C_275, A_276))=k11_relat_1(C_275, A_276) | ~v1_funct_1(C_275) | ~v1_relat_1(C_275) | k11_relat_1(C_275, A_276)=k1_xboole_0 | k1_tarski(k1_funct_1(C_275, A_276))=k11_relat_1(C_275, A_276))), inference(reflexivity, [status(thm), theory('equality')], [c_2007])).
% 22.03/11.50  tff(c_42705, plain, (![C_1722, A_1723]: (~v1_funct_1(C_1722) | ~v1_relat_1(C_1722) | k11_relat_1(C_1722, A_1723)=k1_xboole_0 | k1_tarski(k1_funct_1(C_1722, A_1723))=k11_relat_1(C_1722, A_1723))), inference(factorization, [status(thm), theory('equality')], [c_12873])).
% 22.03/11.50  tff(c_36, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.03/11.50  tff(c_42774, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42705, c_36])).
% 22.03/11.50  tff(c_42793, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_42774])).
% 22.03/11.50  tff(c_42795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_42793])).
% 22.03/11.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.03/11.50  
% 22.03/11.50  Inference rules
% 22.03/11.50  ----------------------
% 22.03/11.50  #Ref     : 1
% 22.03/11.50  #Sup     : 11704
% 22.03/11.50  #Fact    : 18
% 22.03/11.50  #Define  : 0
% 22.03/11.50  #Split   : 10
% 22.03/11.50  #Chain   : 0
% 22.03/11.50  #Close   : 0
% 22.03/11.50  
% 22.03/11.50  Ordering : KBO
% 22.03/11.50  
% 22.03/11.50  Simplification rules
% 22.03/11.50  ----------------------
% 22.03/11.50  #Subsume      : 5039
% 22.03/11.50  #Demod        : 162
% 22.03/11.50  #Tautology    : 766
% 22.03/11.50  #SimpNegUnit  : 121
% 22.03/11.50  #BackRed      : 39
% 22.03/11.50  
% 22.03/11.50  #Partial instantiations: 0
% 22.03/11.50  #Strategies tried      : 1
% 22.03/11.50  
% 22.03/11.50  Timing (in seconds)
% 22.03/11.50  ----------------------
% 22.03/11.50  Preprocessing        : 0.33
% 22.03/11.50  Parsing              : 0.18
% 22.03/11.50  CNF conversion       : 0.02
% 22.03/11.50  Main loop            : 10.38
% 22.03/11.50  Inferencing          : 2.10
% 22.03/11.50  Reduction            : 1.70
% 22.03/11.50  Demodulation         : 1.06
% 22.03/11.50  BG Simplification    : 0.24
% 22.03/11.50  Subsumption          : 5.68
% 22.03/11.50  Abstraction          : 0.36
% 22.03/11.50  MUC search           : 0.00
% 22.03/11.50  Cooper               : 0.00
% 22.03/11.50  Total                : 10.74
% 22.03/11.50  Index Insertion      : 0.00
% 22.03/11.50  Index Deletion       : 0.00
% 22.03/11.50  Index Matching       : 0.00
% 22.03/11.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
