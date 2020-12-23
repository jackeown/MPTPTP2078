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
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   51 (  65 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  85 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_56,C_57,B_58] :
      ( ~ r2_hidden(A_56,C_57)
      | ~ r1_xboole_0(k2_tarski(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_56] : ~ r2_hidden(A_56,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_59] : ~ r2_hidden(A_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_22,plain,(
    ! [A_36] :
      ( v1_relat_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78,c_22])).

tff(c_28,plain,(
    ! [A_37] :
      ( v1_funct_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78,c_28])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_132,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),k1_relat_1(B_86))
      | v5_funct_1(B_86,A_85)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_138,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_85)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_132])).

tff(c_141,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_86,c_138])).

tff(c_143,plain,(
    ! [A_87] :
      ( v5_funct_1(k1_xboole_0,A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_141])).

tff(c_36,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_36])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.20  
% 2.11/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.20  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.11/1.20  
% 2.11/1.20  %Foreground sorts:
% 2.11/1.20  
% 2.11/1.20  
% 2.11/1.20  %Background operators:
% 2.11/1.20  
% 2.11/1.20  
% 2.11/1.20  %Foreground operators:
% 2.11/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.20  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.11/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.20  
% 2.11/1.21  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.11/1.21  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.11/1.21  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.11/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.11/1.21  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.11/1.21  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.11/1.21  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.11/1.21  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.11/1.21  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.11/1.21  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.11/1.21  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.21  tff(c_67, plain, (![A_56, C_57, B_58]: (~r2_hidden(A_56, C_57) | ~r1_xboole_0(k2_tarski(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.21  tff(c_72, plain, (![A_56]: (~r2_hidden(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_67])).
% 2.11/1.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.21  tff(c_73, plain, (![A_59]: (~r2_hidden(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_67])).
% 2.11/1.21  tff(c_78, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.11/1.21  tff(c_22, plain, (![A_36]: (v1_relat_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.21  tff(c_85, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_22])).
% 2.11/1.21  tff(c_28, plain, (![A_37]: (v1_funct_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.21  tff(c_86, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_28])).
% 2.11/1.21  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.21  tff(c_132, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), k1_relat_1(B_86)) | v5_funct_1(B_86, A_85) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.21  tff(c_138, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_85) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_26, c_132])).
% 2.11/1.21  tff(c_141, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_86, c_138])).
% 2.11/1.21  tff(c_143, plain, (![A_87]: (v5_funct_1(k1_xboole_0, A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(negUnitSimplification, [status(thm)], [c_72, c_141])).
% 2.11/1.21  tff(c_36, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.11/1.21  tff(c_146, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_143, c_36])).
% 2.11/1.21  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_146])).
% 2.11/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.21  
% 2.11/1.21  Inference rules
% 2.11/1.21  ----------------------
% 2.11/1.21  #Ref     : 0
% 2.11/1.21  #Sup     : 24
% 2.11/1.21  #Fact    : 0
% 2.11/1.21  #Define  : 0
% 2.11/1.21  #Split   : 0
% 2.11/1.21  #Chain   : 0
% 2.11/1.21  #Close   : 0
% 2.11/1.21  
% 2.11/1.21  Ordering : KBO
% 2.11/1.21  
% 2.11/1.21  Simplification rules
% 2.11/1.21  ----------------------
% 2.11/1.21  #Subsume      : 0
% 2.11/1.21  #Demod        : 4
% 2.11/1.21  #Tautology    : 17
% 2.11/1.21  #SimpNegUnit  : 1
% 2.11/1.21  #BackRed      : 0
% 2.11/1.21  
% 2.11/1.21  #Partial instantiations: 0
% 2.11/1.21  #Strategies tried      : 1
% 2.11/1.21  
% 2.11/1.21  Timing (in seconds)
% 2.11/1.21  ----------------------
% 2.11/1.22  Preprocessing        : 0.32
% 2.11/1.22  Parsing              : 0.17
% 2.11/1.22  CNF conversion       : 0.02
% 2.11/1.22  Main loop            : 0.13
% 2.11/1.22  Inferencing          : 0.06
% 2.11/1.22  Reduction            : 0.04
% 2.11/1.22  Demodulation         : 0.03
% 2.11/1.22  BG Simplification    : 0.01
% 2.11/1.22  Subsumption          : 0.01
% 2.11/1.22  Abstraction          : 0.01
% 2.11/1.22  MUC search           : 0.00
% 2.11/1.22  Cooper               : 0.00
% 2.11/1.22  Total                : 0.48
% 2.11/1.22  Index Insertion      : 0.00
% 2.11/1.22  Index Deletion       : 0.00
% 2.11/1.22  Index Matching       : 0.00
% 2.11/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
