%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 267 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  113 ( 466 expanded)
%              Number of equality atoms :   40 ( 156 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_26] : v1_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_27] :
      ( k1_relat_1(k6_relat_1(A_27)) = A_27
      | ~ v1_funct_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    ! [A_27] :
      ( k1_relat_1(k6_relat_1(A_27)) = A_27
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_56,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_149,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_158,plain,(
    ! [A_27] :
      ( k7_relat_1(k6_relat_1(A_27),A_27) = k6_relat_1(A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_149])).

tff(c_177,plain,(
    ! [A_45] : k7_relat_1(k6_relat_1(A_45),A_45) = k6_relat_1(A_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_109,plain,(
    ! [A_39] :
      ( k7_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_116,plain,(
    ! [A_26] : k7_relat_1(k6_relat_1(A_26),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_184,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_116])).

tff(c_210,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_32])).

tff(c_89,plain,(
    ! [A_37] :
      ( k9_relat_1(A_37,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_96,plain,(
    ! [A_26] : k9_relat_1(k6_relat_1(A_26),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_320,plain,(
    ! [B_51,A_52] :
      ( k2_relat_1(k7_relat_1(B_51,A_52)) = k9_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_338,plain,(
    ! [A_26] :
      ( k9_relat_1(k6_relat_1(A_26),k1_xboole_0) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_320])).

tff(c_349,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96,c_338])).

tff(c_268,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_relat_1(A_48),B_49) = k7_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_129,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [A_26] : k5_relat_1(k6_relat_1(A_26),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_129])).

tff(c_275,plain,(
    ! [A_48] :
      ( k7_relat_1(k1_xboole_0,A_48) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_136])).

tff(c_287,plain,(
    ! [A_48] : k7_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_275])).

tff(c_329,plain,(
    ! [A_48] :
      ( k9_relat_1(k1_xboole_0,A_48) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_320])).

tff(c_345,plain,(
    ! [A_48] : k9_relat_1(k1_xboole_0,A_48) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_329])).

tff(c_373,plain,(
    ! [A_55] : k9_relat_1(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_345])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k9_relat_1(A_1,k1_tarski(B_3)) = k11_relat_1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_379,plain,(
    ! [B_3] :
      ( k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_2])).

tff(c_396,plain,(
    ! [B_3] : k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_379])).

tff(c_208,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_56])).

tff(c_424,plain,(
    ! [B_59,A_60] :
      ( k11_relat_1(B_59,A_60) != k1_xboole_0
      | ~ r2_hidden(A_60,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_430,plain,(
    ! [A_60] :
      ( k11_relat_1(k1_xboole_0,A_60) != k1_xboole_0
      | ~ r2_hidden(A_60,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_424])).

tff(c_436,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_396,c_430])).

tff(c_212,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_34])).

tff(c_545,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),k1_relat_1(B_70))
      | v5_funct_1(B_70,A_69)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_551,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_1'(A_69,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_69)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_545])).

tff(c_557,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_1'(A_69,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_212,c_551])).

tff(c_561,plain,(
    ! [A_71] :
      ( v5_funct_1(k1_xboole_0,A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_557])).

tff(c_44,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_564,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_561,c_44])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.22/1.29  
% 2.22/1.29  %Foreground sorts:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Background operators:
% 2.22/1.29  
% 2.22/1.29  
% 2.22/1.29  %Foreground operators:
% 2.22/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.29  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.22/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.29  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.22/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.29  
% 2.53/1.30  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.53/1.30  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.53/1.30  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.53/1.30  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.53/1.30  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.53/1.30  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 2.53/1.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.53/1.30  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.53/1.30  tff(f_61, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.53/1.30  tff(f_30, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.53/1.30  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.53/1.30  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.53/1.30  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.30  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.30  tff(c_32, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.53/1.30  tff(c_34, plain, (![A_26]: (v1_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.53/1.30  tff(c_42, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27 | ~v1_funct_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.53/1.30  tff(c_50, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27 | ~v1_relat_1(k6_relat_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 2.53/1.30  tff(c_56, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50])).
% 2.53/1.30  tff(c_149, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.30  tff(c_158, plain, (![A_27]: (k7_relat_1(k6_relat_1(A_27), A_27)=k6_relat_1(A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_149])).
% 2.53/1.30  tff(c_177, plain, (![A_45]: (k7_relat_1(k6_relat_1(A_45), A_45)=k6_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_158])).
% 2.53/1.30  tff(c_109, plain, (![A_39]: (k7_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.30  tff(c_116, plain, (![A_26]: (k7_relat_1(k6_relat_1(A_26), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_109])).
% 2.53/1.30  tff(c_184, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_177, c_116])).
% 2.53/1.30  tff(c_210, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_32])).
% 2.53/1.30  tff(c_89, plain, (![A_37]: (k9_relat_1(A_37, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.53/1.30  tff(c_96, plain, (![A_26]: (k9_relat_1(k6_relat_1(A_26), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_89])).
% 2.53/1.30  tff(c_320, plain, (![B_51, A_52]: (k2_relat_1(k7_relat_1(B_51, A_52))=k9_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.30  tff(c_338, plain, (![A_26]: (k9_relat_1(k6_relat_1(A_26), k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_320])).
% 2.53/1.30  tff(c_349, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96, c_338])).
% 2.53/1.30  tff(c_268, plain, (![A_48, B_49]: (k5_relat_1(k6_relat_1(A_48), B_49)=k7_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.30  tff(c_129, plain, (![A_41]: (k5_relat_1(A_41, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.30  tff(c_136, plain, (![A_26]: (k5_relat_1(k6_relat_1(A_26), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_129])).
% 2.53/1.30  tff(c_275, plain, (![A_48]: (k7_relat_1(k1_xboole_0, A_48)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_268, c_136])).
% 2.53/1.30  tff(c_287, plain, (![A_48]: (k7_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_275])).
% 2.53/1.30  tff(c_329, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_287, c_320])).
% 2.53/1.30  tff(c_345, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_329])).
% 2.53/1.30  tff(c_373, plain, (![A_55]: (k9_relat_1(k1_xboole_0, A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_345])).
% 2.53/1.30  tff(c_2, plain, (![A_1, B_3]: (k9_relat_1(A_1, k1_tarski(B_3))=k11_relat_1(A_1, B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.53/1.30  tff(c_379, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_373, c_2])).
% 2.53/1.30  tff(c_396, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_379])).
% 2.53/1.30  tff(c_208, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_184, c_56])).
% 2.53/1.30  tff(c_424, plain, (![B_59, A_60]: (k11_relat_1(B_59, A_60)!=k1_xboole_0 | ~r2_hidden(A_60, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.30  tff(c_430, plain, (![A_60]: (k11_relat_1(k1_xboole_0, A_60)!=k1_xboole_0 | ~r2_hidden(A_60, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_424])).
% 2.53/1.30  tff(c_436, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_396, c_430])).
% 2.53/1.30  tff(c_212, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_34])).
% 2.53/1.30  tff(c_545, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), k1_relat_1(B_70)) | v5_funct_1(B_70, A_69) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.30  tff(c_551, plain, (![A_69]: (r2_hidden('#skF_1'(A_69, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_69) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_208, c_545])).
% 2.53/1.30  tff(c_557, plain, (![A_69]: (r2_hidden('#skF_1'(A_69, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_212, c_551])).
% 2.53/1.30  tff(c_561, plain, (![A_71]: (v5_funct_1(k1_xboole_0, A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(negUnitSimplification, [status(thm)], [c_436, c_557])).
% 2.53/1.30  tff(c_44, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.30  tff(c_564, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_561, c_44])).
% 2.53/1.30  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_564])).
% 2.53/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.30  
% 2.53/1.30  Inference rules
% 2.53/1.30  ----------------------
% 2.53/1.30  #Ref     : 0
% 2.53/1.30  #Sup     : 120
% 2.53/1.30  #Fact    : 0
% 2.53/1.30  #Define  : 0
% 2.53/1.30  #Split   : 0
% 2.53/1.30  #Chain   : 0
% 2.53/1.30  #Close   : 0
% 2.53/1.30  
% 2.53/1.30  Ordering : KBO
% 2.53/1.30  
% 2.53/1.30  Simplification rules
% 2.53/1.30  ----------------------
% 2.53/1.30  #Subsume      : 3
% 2.53/1.30  #Demod        : 90
% 2.53/1.30  #Tautology    : 88
% 2.53/1.30  #SimpNegUnit  : 5
% 2.53/1.30  #BackRed      : 0
% 2.53/1.30  
% 2.53/1.30  #Partial instantiations: 0
% 2.53/1.30  #Strategies tried      : 1
% 2.53/1.30  
% 2.53/1.30  Timing (in seconds)
% 2.53/1.30  ----------------------
% 2.53/1.31  Preprocessing        : 0.31
% 2.53/1.31  Parsing              : 0.17
% 2.53/1.31  CNF conversion       : 0.02
% 2.53/1.31  Main loop            : 0.24
% 2.53/1.31  Inferencing          : 0.10
% 2.53/1.31  Reduction            : 0.08
% 2.53/1.31  Demodulation         : 0.06
% 2.53/1.31  BG Simplification    : 0.02
% 2.53/1.31  Subsumption          : 0.03
% 2.53/1.31  Abstraction          : 0.01
% 2.53/1.31  MUC search           : 0.00
% 2.53/1.31  Cooper               : 0.00
% 2.53/1.31  Total                : 0.58
% 2.53/1.31  Index Insertion      : 0.00
% 2.53/1.31  Index Deletion       : 0.00
% 2.53/1.31  Index Matching       : 0.00
% 2.53/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
