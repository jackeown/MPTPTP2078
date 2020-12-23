%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 105 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 225 expanded)
%              Number of equality atoms :   25 ( 102 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_66,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_30,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_54,axiom,(
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

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1('#skF_2'(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_13] : v1_relat_1('#skF_2'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_13] :
      ( k1_relat_1('#skF_2'(A_13)) != k1_xboole_0
      | '#skF_2'(A_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_82,plain,(
    ! [A_27] :
      ( k1_xboole_0 != A_27
      | '#skF_2'(A_27) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_92,plain,(
    ! [A_27] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_121,plain,(
    ! [A_27] : k1_xboole_0 != A_27 ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2,plain,(
    ! [A_1] : k10_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_2])).

tff(c_130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_4,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_166,plain,(
    ! [B_35,A_36] :
      ( k10_relat_1(B_35,k1_tarski(A_36)) != k1_xboole_0
      | ~ r2_hidden(A_36,k2_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_169,plain,(
    ! [A_36] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_36)) != k1_xboole_0
      | ~ r2_hidden(A_36,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_166])).

tff(c_171,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2,c_169])).

tff(c_22,plain,(
    ! [A_13] : v1_funct_1('#skF_2'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    ! [A_27] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_22])).

tff(c_99,plain,(
    ! [A_27] : k1_xboole_0 != A_27 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2])).

tff(c_120,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_211,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),k1_relat_1(B_43))
      | v5_funct_1(B_43,A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_220,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_211])).

tff(c_225,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_120,c_220])).

tff(c_227,plain,(
    ! [A_44] :
      ( v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_225])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_230,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_227,c_30])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.18  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.18  
% 1.68/1.18  %Foreground sorts:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Background operators:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Foreground operators:
% 1.68/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.18  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.68/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.18  
% 1.96/1.19  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.96/1.19  tff(f_66, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 1.96/1.19  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.96/1.19  tff(f_27, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.96/1.19  tff(f_30, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.96/1.19  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 1.96/1.19  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.96/1.19  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.19  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.19  tff(c_20, plain, (![A_13]: (k1_relat_1('#skF_2'(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.19  tff(c_24, plain, (![A_13]: (v1_relat_1('#skF_2'(A_13)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.19  tff(c_71, plain, (![A_26]: (k1_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.19  tff(c_74, plain, (![A_13]: (k1_relat_1('#skF_2'(A_13))!=k1_xboole_0 | '#skF_2'(A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_71])).
% 1.96/1.19  tff(c_82, plain, (![A_27]: (k1_xboole_0!=A_27 | '#skF_2'(A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_74])).
% 1.96/1.19  tff(c_92, plain, (![A_27]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_27)), inference(superposition, [status(thm), theory('equality')], [c_82, c_24])).
% 1.96/1.19  tff(c_121, plain, (![A_27]: (k1_xboole_0!=A_27)), inference(splitLeft, [status(thm)], [c_92])).
% 1.96/1.19  tff(c_2, plain, (![A_1]: (k10_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.19  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_2])).
% 1.96/1.19  tff(c_130, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_92])).
% 1.96/1.19  tff(c_4, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.96/1.19  tff(c_166, plain, (![B_35, A_36]: (k10_relat_1(B_35, k1_tarski(A_36))!=k1_xboole_0 | ~r2_hidden(A_36, k2_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.96/1.19  tff(c_169, plain, (![A_36]: (k10_relat_1(k1_xboole_0, k1_tarski(A_36))!=k1_xboole_0 | ~r2_hidden(A_36, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_166])).
% 1.96/1.19  tff(c_171, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_2, c_169])).
% 1.96/1.19  tff(c_22, plain, (![A_13]: (v1_funct_1('#skF_2'(A_13)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.19  tff(c_90, plain, (![A_27]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_27)), inference(superposition, [status(thm), theory('equality')], [c_82, c_22])).
% 1.96/1.19  tff(c_99, plain, (![A_27]: (k1_xboole_0!=A_27)), inference(splitLeft, [status(thm)], [c_90])).
% 1.96/1.19  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2])).
% 1.96/1.19  tff(c_120, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_90])).
% 1.96/1.19  tff(c_6, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.96/1.19  tff(c_211, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), k1_relat_1(B_43)) | v5_funct_1(B_43, A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.19  tff(c_220, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_211])).
% 1.96/1.19  tff(c_225, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_120, c_220])).
% 1.96/1.19  tff(c_227, plain, (![A_44]: (v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(negUnitSimplification, [status(thm)], [c_171, c_225])).
% 1.96/1.19  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.19  tff(c_230, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_227, c_30])).
% 1.96/1.19  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_230])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 38
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 5
% 1.96/1.19  #Chain   : 0
% 1.96/1.19  #Close   : 0
% 1.96/1.19  
% 1.96/1.19  Ordering : KBO
% 1.96/1.19  
% 1.96/1.19  Simplification rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Subsume      : 9
% 1.96/1.19  #Demod        : 19
% 1.96/1.19  #Tautology    : 23
% 1.96/1.19  #SimpNegUnit  : 15
% 1.96/1.19  #BackRed      : 7
% 1.96/1.19  
% 1.96/1.19  #Partial instantiations: 0
% 1.96/1.19  #Strategies tried      : 1
% 1.96/1.19  
% 1.96/1.19  Timing (in seconds)
% 1.96/1.19  ----------------------
% 1.96/1.19  Preprocessing        : 0.27
% 1.96/1.19  Parsing              : 0.15
% 1.96/1.19  CNF conversion       : 0.02
% 1.96/1.19  Main loop            : 0.17
% 1.96/1.19  Inferencing          : 0.06
% 1.96/1.19  Reduction            : 0.05
% 1.96/1.19  Demodulation         : 0.03
% 1.96/1.19  BG Simplification    : 0.01
% 1.96/1.19  Subsumption          : 0.03
% 1.96/1.19  Abstraction          : 0.01
% 1.96/1.19  MUC search           : 0.00
% 1.96/1.19  Cooper               : 0.00
% 1.96/1.19  Total                : 0.46
% 1.96/1.19  Index Insertion      : 0.00
% 1.96/1.19  Index Deletion       : 0.00
% 1.96/1.19  Index Matching       : 0.00
% 1.96/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
