%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:23 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 225 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [A_38,C_39] :
      ( r2_hidden(k4_tarski(A_38,k1_funct_1(C_39,A_38)),C_39)
      | ~ r2_hidden(A_38,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [B_7,C_8,A_6] :
      ( r2_hidden(B_7,k11_relat_1(C_8,A_6))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [C_39,A_38] :
      ( r2_hidden(k1_funct_1(C_39,A_38),k11_relat_1(C_39,A_38))
      | ~ r2_hidden(A_38,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ r2_hidden(B_7,k11_relat_1(C_8,A_6))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [C_27,A_28,B_29] :
      ( k1_funct_1(C_27,A_28) = B_29
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [C_43,A_44,B_45] :
      ( k1_funct_1(C_43,A_44) = B_45
      | ~ v1_funct_1(C_43)
      | ~ r2_hidden(B_45,k11_relat_1(C_43,A_44))
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_452,plain,(
    ! [A_80,C_81,A_82] :
      ( '#skF_2'(A_80,k11_relat_1(C_81,A_82)) = k1_funct_1(C_81,A_82)
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81)
      | '#skF_1'(A_80,k11_relat_1(C_81,A_82)) = A_80
      | k1_tarski(A_80) = k11_relat_1(C_81,A_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_463,plain,(
    ! [A_80,C_81,A_82] :
      ( '#skF_1'(A_80,k11_relat_1(C_81,A_82)) = A_80
      | k1_funct_1(C_81,A_82) != A_80
      | k1_tarski(A_80) = k11_relat_1(C_81,A_82)
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81)
      | '#skF_1'(A_80,k11_relat_1(C_81,A_82)) = A_80
      | k1_tarski(A_80) = k11_relat_1(C_81,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_8])).

tff(c_1357,plain,(
    ! [C_157,A_158,A_159] :
      ( k1_funct_1(C_157,A_158) != A_159
      | ~ v1_funct_1(C_157)
      | ~ v1_relat_1(C_157)
      | k1_tarski(A_159) = k11_relat_1(C_157,A_158)
      | '#skF_1'(A_159,k11_relat_1(C_157,A_158)) = A_159 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_463])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [A_1,C_43,A_44] :
      ( '#skF_2'(A_1,k11_relat_1(C_43,A_44)) = k1_funct_1(C_43,A_44)
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43)
      | ~ r2_hidden('#skF_1'(A_1,k11_relat_1(C_43,A_44)),k11_relat_1(C_43,A_44))
      | k1_tarski(A_1) = k11_relat_1(C_43,A_44) ) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_3901,plain,(
    ! [A_289,C_290,A_291] :
      ( '#skF_2'(A_289,k11_relat_1(C_290,A_291)) = k1_funct_1(C_290,A_291)
      | ~ v1_funct_1(C_290)
      | ~ v1_relat_1(C_290)
      | ~ r2_hidden(A_289,k11_relat_1(C_290,A_291))
      | k1_tarski(A_289) = k11_relat_1(C_290,A_291)
      | k1_funct_1(C_290,A_291) != A_289
      | ~ v1_funct_1(C_290)
      | ~ v1_relat_1(C_290)
      | k1_tarski(A_289) = k11_relat_1(C_290,A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_163])).

tff(c_3989,plain,(
    ! [C_295,A_296] :
      ( '#skF_2'(k1_funct_1(C_295,A_296),k11_relat_1(C_295,A_296)) = k1_funct_1(C_295,A_296)
      | k1_tarski(k1_funct_1(C_295,A_296)) = k11_relat_1(C_295,A_296)
      | ~ r2_hidden(A_296,k1_relat_1(C_295))
      | ~ v1_funct_1(C_295)
      | ~ v1_relat_1(C_295) ) ),
    inference(resolution,[status(thm)],[c_126,c_3901])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1421,plain,(
    ! [A_160,C_161,A_162] :
      ( ~ r2_hidden(A_160,k11_relat_1(C_161,A_162))
      | '#skF_2'(A_160,k11_relat_1(C_161,A_162)) != A_160
      | k1_tarski(A_160) = k11_relat_1(C_161,A_162)
      | k1_funct_1(C_161,A_162) != A_160
      | ~ v1_funct_1(C_161)
      | ~ v1_relat_1(C_161)
      | k1_tarski(A_160) = k11_relat_1(C_161,A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_6])).

tff(c_1456,plain,(
    ! [C_39,A_38] :
      ( '#skF_2'(k1_funct_1(C_39,A_38),k11_relat_1(C_39,A_38)) != k1_funct_1(C_39,A_38)
      | k1_tarski(k1_funct_1(C_39,A_38)) = k11_relat_1(C_39,A_38)
      | ~ r2_hidden(A_38,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_126,c_1421])).

tff(c_4039,plain,(
    ! [C_297,A_298] :
      ( k1_tarski(k1_funct_1(C_297,A_298)) = k11_relat_1(C_297,A_298)
      | ~ r2_hidden(A_298,k1_relat_1(C_297))
      | ~ v1_funct_1(C_297)
      | ~ v1_relat_1(C_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3989,c_1456])).

tff(c_4073,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_4039])).

tff(c_4085,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4073])).

tff(c_4087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_4085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:49:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.44  
% 6.90/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.44  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.90/2.44  
% 6.90/2.44  %Foreground sorts:
% 6.90/2.44  
% 6.90/2.44  
% 6.90/2.44  %Background operators:
% 6.90/2.44  
% 6.90/2.44  
% 6.90/2.44  %Foreground operators:
% 6.90/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.90/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.90/2.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.90/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.90/2.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.90/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.90/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.90/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.90/2.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.90/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.90/2.44  
% 6.90/2.45  tff(f_57, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 6.90/2.45  tff(f_48, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 6.90/2.45  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 6.90/2.45  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.90/2.45  tff(c_24, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.45  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.45  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.45  tff(c_26, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.90/2.45  tff(c_104, plain, (![A_38, C_39]: (r2_hidden(k4_tarski(A_38, k1_funct_1(C_39, A_38)), C_39) | ~r2_hidden(A_38, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.90/2.45  tff(c_16, plain, (![B_7, C_8, A_6]: (r2_hidden(B_7, k11_relat_1(C_8, A_6)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.45  tff(c_126, plain, (![C_39, A_38]: (r2_hidden(k1_funct_1(C_39, A_38), k11_relat_1(C_39, A_38)) | ~r2_hidden(A_38, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_104, c_16])).
% 6.90/2.45  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.45  tff(c_14, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski(A_6, B_7), C_8) | ~r2_hidden(B_7, k11_relat_1(C_8, A_6)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.45  tff(c_62, plain, (![C_27, A_28, B_29]: (k1_funct_1(C_27, A_28)=B_29 | ~r2_hidden(k4_tarski(A_28, B_29), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.90/2.45  tff(c_145, plain, (![C_43, A_44, B_45]: (k1_funct_1(C_43, A_44)=B_45 | ~v1_funct_1(C_43) | ~r2_hidden(B_45, k11_relat_1(C_43, A_44)) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_14, c_62])).
% 6.90/2.45  tff(c_452, plain, (![A_80, C_81, A_82]: ('#skF_2'(A_80, k11_relat_1(C_81, A_82))=k1_funct_1(C_81, A_82) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81) | '#skF_1'(A_80, k11_relat_1(C_81, A_82))=A_80 | k1_tarski(A_80)=k11_relat_1(C_81, A_82))), inference(resolution, [status(thm)], [c_12, c_145])).
% 6.90/2.45  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.45  tff(c_463, plain, (![A_80, C_81, A_82]: ('#skF_1'(A_80, k11_relat_1(C_81, A_82))=A_80 | k1_funct_1(C_81, A_82)!=A_80 | k1_tarski(A_80)=k11_relat_1(C_81, A_82) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81) | '#skF_1'(A_80, k11_relat_1(C_81, A_82))=A_80 | k1_tarski(A_80)=k11_relat_1(C_81, A_82))), inference(superposition, [status(thm), theory('equality')], [c_452, c_8])).
% 6.90/2.45  tff(c_1357, plain, (![C_157, A_158, A_159]: (k1_funct_1(C_157, A_158)!=A_159 | ~v1_funct_1(C_157) | ~v1_relat_1(C_157) | k1_tarski(A_159)=k11_relat_1(C_157, A_158) | '#skF_1'(A_159, k11_relat_1(C_157, A_158))=A_159)), inference(factorization, [status(thm), theory('equality')], [c_463])).
% 6.90/2.45  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.45  tff(c_163, plain, (![A_1, C_43, A_44]: ('#skF_2'(A_1, k11_relat_1(C_43, A_44))=k1_funct_1(C_43, A_44) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43) | ~r2_hidden('#skF_1'(A_1, k11_relat_1(C_43, A_44)), k11_relat_1(C_43, A_44)) | k1_tarski(A_1)=k11_relat_1(C_43, A_44))), inference(resolution, [status(thm)], [c_10, c_145])).
% 6.90/2.45  tff(c_3901, plain, (![A_289, C_290, A_291]: ('#skF_2'(A_289, k11_relat_1(C_290, A_291))=k1_funct_1(C_290, A_291) | ~v1_funct_1(C_290) | ~v1_relat_1(C_290) | ~r2_hidden(A_289, k11_relat_1(C_290, A_291)) | k1_tarski(A_289)=k11_relat_1(C_290, A_291) | k1_funct_1(C_290, A_291)!=A_289 | ~v1_funct_1(C_290) | ~v1_relat_1(C_290) | k1_tarski(A_289)=k11_relat_1(C_290, A_291))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_163])).
% 6.90/2.45  tff(c_3989, plain, (![C_295, A_296]: ('#skF_2'(k1_funct_1(C_295, A_296), k11_relat_1(C_295, A_296))=k1_funct_1(C_295, A_296) | k1_tarski(k1_funct_1(C_295, A_296))=k11_relat_1(C_295, A_296) | ~r2_hidden(A_296, k1_relat_1(C_295)) | ~v1_funct_1(C_295) | ~v1_relat_1(C_295))), inference(resolution, [status(thm)], [c_126, c_3901])).
% 6.90/2.45  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.90/2.45  tff(c_1421, plain, (![A_160, C_161, A_162]: (~r2_hidden(A_160, k11_relat_1(C_161, A_162)) | '#skF_2'(A_160, k11_relat_1(C_161, A_162))!=A_160 | k1_tarski(A_160)=k11_relat_1(C_161, A_162) | k1_funct_1(C_161, A_162)!=A_160 | ~v1_funct_1(C_161) | ~v1_relat_1(C_161) | k1_tarski(A_160)=k11_relat_1(C_161, A_162))), inference(superposition, [status(thm), theory('equality')], [c_1357, c_6])).
% 6.90/2.45  tff(c_1456, plain, (![C_39, A_38]: ('#skF_2'(k1_funct_1(C_39, A_38), k11_relat_1(C_39, A_38))!=k1_funct_1(C_39, A_38) | k1_tarski(k1_funct_1(C_39, A_38))=k11_relat_1(C_39, A_38) | ~r2_hidden(A_38, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_126, c_1421])).
% 6.90/2.45  tff(c_4039, plain, (![C_297, A_298]: (k1_tarski(k1_funct_1(C_297, A_298))=k11_relat_1(C_297, A_298) | ~r2_hidden(A_298, k1_relat_1(C_297)) | ~v1_funct_1(C_297) | ~v1_relat_1(C_297))), inference(superposition, [status(thm), theory('equality')], [c_3989, c_1456])).
% 6.90/2.45  tff(c_4073, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_4039])).
% 6.90/2.45  tff(c_4085, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4073])).
% 6.90/2.45  tff(c_4087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_4085])).
% 6.90/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.45  
% 6.90/2.45  Inference rules
% 6.90/2.45  ----------------------
% 6.90/2.45  #Ref     : 0
% 6.90/2.45  #Sup     : 1026
% 6.90/2.45  #Fact    : 4
% 6.90/2.45  #Define  : 0
% 6.90/2.45  #Split   : 1
% 6.90/2.45  #Chain   : 0
% 6.90/2.45  #Close   : 0
% 6.90/2.45  
% 6.90/2.45  Ordering : KBO
% 6.90/2.45  
% 6.90/2.45  Simplification rules
% 6.90/2.45  ----------------------
% 6.90/2.45  #Subsume      : 163
% 6.90/2.45  #Demod        : 30
% 6.90/2.45  #Tautology    : 201
% 6.90/2.45  #SimpNegUnit  : 1
% 6.90/2.45  #BackRed      : 0
% 6.90/2.45  
% 6.90/2.45  #Partial instantiations: 0
% 6.90/2.45  #Strategies tried      : 1
% 6.90/2.45  
% 6.90/2.45  Timing (in seconds)
% 6.90/2.45  ----------------------
% 7.09/2.46  Preprocessing        : 0.27
% 7.09/2.46  Parsing              : 0.15
% 7.09/2.46  CNF conversion       : 0.02
% 7.09/2.46  Main loop            : 1.40
% 7.09/2.46  Inferencing          : 0.48
% 7.09/2.46  Reduction            : 0.30
% 7.09/2.46  Demodulation         : 0.20
% 7.09/2.46  BG Simplification    : 0.08
% 7.09/2.46  Subsumption          : 0.45
% 7.09/2.46  Abstraction          : 0.11
% 7.09/2.46  MUC search           : 0.00
% 7.09/2.46  Cooper               : 0.00
% 7.09/2.46  Total                : 1.69
% 7.09/2.46  Index Insertion      : 0.00
% 7.09/2.46  Index Deletion       : 0.00
% 7.09/2.46  Index Matching       : 0.00
% 7.09/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
