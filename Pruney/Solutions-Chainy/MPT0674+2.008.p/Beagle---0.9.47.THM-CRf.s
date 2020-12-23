%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:23 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 189 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  114 ( 558 expanded)
%              Number of equality atoms :   55 ( 201 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    ! [B_37,A_38] :
      ( r2_hidden(k4_tarski(B_37,k1_funct_1(A_38,B_37)),A_38)
      | ~ r2_hidden(B_37,k1_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [B_8,C_9,A_7] :
      ( r2_hidden(B_8,k11_relat_1(C_9,A_7))
      | ~ r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_38,B_37] :
      ( r2_hidden(k1_funct_1(A_38,B_37),k11_relat_1(A_38,B_37))
      | ~ r2_hidden(B_37,k1_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_98,c_18])).

tff(c_28,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ r2_hidden(B_8,k11_relat_1(C_9,A_7))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_163,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_funct_1(A_46,B_47) = C_48
      | ~ r2_hidden(k4_tarski(B_47,C_48),A_46)
      | ~ r2_hidden(B_47,k1_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_189,plain,(
    ! [C_51,A_52,B_53] :
      ( k1_funct_1(C_51,A_52) = B_53
      | ~ r2_hidden(A_52,k1_relat_1(C_51))
      | ~ v1_funct_1(C_51)
      | ~ r2_hidden(B_53,k11_relat_1(C_51,A_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_163])).

tff(c_205,plain,(
    ! [B_53] :
      ( k1_funct_1('#skF_4','#skF_3') = B_53
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(B_53,k11_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_189])).

tff(c_214,plain,(
    ! [B_54] :
      ( k1_funct_1('#skF_4','#skF_3') = B_54
      | ~ r2_hidden(B_54,k11_relat_1('#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_205])).

tff(c_322,plain,(
    ! [A_62] :
      ( '#skF_2'(A_62,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_62,k11_relat_1('#skF_4','#skF_3')) = A_62
      | k1_tarski(A_62) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [A_62] :
      ( '#skF_1'(A_62,k11_relat_1('#skF_4','#skF_3')) = A_62
      | k1_funct_1('#skF_4','#skF_3') != A_62
      | k1_tarski(A_62) = k11_relat_1('#skF_4','#skF_3')
      | '#skF_1'(A_62,k11_relat_1('#skF_4','#skF_3')) = A_62
      | k1_tarski(A_62) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_8])).

tff(c_656,plain,(
    ! [A_105] :
      ( k1_funct_1('#skF_4','#skF_3') != A_105
      | k1_tarski(A_105) = k11_relat_1('#skF_4','#skF_3')
      | '#skF_1'(A_105,k11_relat_1('#skF_4','#skF_3')) = A_105 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_333])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_672,plain,(
    ! [A_106] :
      ( ~ r2_hidden(A_106,k11_relat_1('#skF_4','#skF_3'))
      | '#skF_2'(A_106,k11_relat_1('#skF_4','#skF_3')) != A_106
      | k1_tarski(A_106) = k11_relat_1('#skF_4','#skF_3')
      | k1_funct_1('#skF_4','#skF_3') != A_106
      | k1_tarski(A_106) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_6])).

tff(c_683,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_672])).

tff(c_708,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_683])).

tff(c_709,plain,(
    '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_708])).

tff(c_331,plain,(
    ! [A_62] :
      ( '#skF_1'(A_62,k11_relat_1('#skF_4','#skF_3')) = A_62
      | r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3'))
      | k1_tarski(A_62) = k11_relat_1('#skF_4','#skF_3')
      | '#skF_1'(A_62,k11_relat_1('#skF_4','#skF_3')) = A_62
      | k1_tarski(A_62) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_12])).

tff(c_641,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_242,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_1,k11_relat_1('#skF_4','#skF_3')) = A_1
      | k1_tarski(A_1) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_716,plain,
    ( '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_709])).

tff(c_719,plain,(
    '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_716])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_240,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,k11_relat_1('#skF_4','#skF_3')),k11_relat_1('#skF_4','#skF_3'))
      | k1_tarski(A_1) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_214])).

tff(c_759,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3'))
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_240])).

tff(c_773,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_759])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_709,c_773])).

tff(c_777,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_780,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_777])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_780])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.44  
% 2.75/1.44  %Foreground sorts:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Background operators:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Foreground operators:
% 2.75/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.75/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.44  
% 2.75/1.45  tff(f_67, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.75/1.45  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.75/1.45  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.75/1.45  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.75/1.45  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.45  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.45  tff(c_30, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.45  tff(c_98, plain, (![B_37, A_38]: (r2_hidden(k4_tarski(B_37, k1_funct_1(A_38, B_37)), A_38) | ~r2_hidden(B_37, k1_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.45  tff(c_18, plain, (![B_8, C_9, A_7]: (r2_hidden(B_8, k11_relat_1(C_9, A_7)) | ~r2_hidden(k4_tarski(A_7, B_8), C_9) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.45  tff(c_106, plain, (![A_38, B_37]: (r2_hidden(k1_funct_1(A_38, B_37), k11_relat_1(A_38, B_37)) | ~r2_hidden(B_37, k1_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_98, c_18])).
% 2.75/1.45  tff(c_28, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.45  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.45  tff(c_16, plain, (![A_7, B_8, C_9]: (r2_hidden(k4_tarski(A_7, B_8), C_9) | ~r2_hidden(B_8, k11_relat_1(C_9, A_7)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.45  tff(c_163, plain, (![A_46, B_47, C_48]: (k1_funct_1(A_46, B_47)=C_48 | ~r2_hidden(k4_tarski(B_47, C_48), A_46) | ~r2_hidden(B_47, k1_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.45  tff(c_189, plain, (![C_51, A_52, B_53]: (k1_funct_1(C_51, A_52)=B_53 | ~r2_hidden(A_52, k1_relat_1(C_51)) | ~v1_funct_1(C_51) | ~r2_hidden(B_53, k11_relat_1(C_51, A_52)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_16, c_163])).
% 2.75/1.45  tff(c_205, plain, (![B_53]: (k1_funct_1('#skF_4', '#skF_3')=B_53 | ~v1_funct_1('#skF_4') | ~r2_hidden(B_53, k11_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_189])).
% 2.75/1.45  tff(c_214, plain, (![B_54]: (k1_funct_1('#skF_4', '#skF_3')=B_54 | ~r2_hidden(B_54, k11_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_205])).
% 2.75/1.45  tff(c_322, plain, (![A_62]: ('#skF_2'(A_62, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_62, k11_relat_1('#skF_4', '#skF_3'))=A_62 | k1_tarski(A_62)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_214])).
% 2.75/1.45  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.45  tff(c_333, plain, (![A_62]: ('#skF_1'(A_62, k11_relat_1('#skF_4', '#skF_3'))=A_62 | k1_funct_1('#skF_4', '#skF_3')!=A_62 | k1_tarski(A_62)=k11_relat_1('#skF_4', '#skF_3') | '#skF_1'(A_62, k11_relat_1('#skF_4', '#skF_3'))=A_62 | k1_tarski(A_62)=k11_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_8])).
% 2.75/1.45  tff(c_656, plain, (![A_105]: (k1_funct_1('#skF_4', '#skF_3')!=A_105 | k1_tarski(A_105)=k11_relat_1('#skF_4', '#skF_3') | '#skF_1'(A_105, k11_relat_1('#skF_4', '#skF_3'))=A_105)), inference(factorization, [status(thm), theory('equality')], [c_333])).
% 2.75/1.45  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.45  tff(c_672, plain, (![A_106]: (~r2_hidden(A_106, k11_relat_1('#skF_4', '#skF_3')) | '#skF_2'(A_106, k11_relat_1('#skF_4', '#skF_3'))!=A_106 | k1_tarski(A_106)=k11_relat_1('#skF_4', '#skF_3') | k1_funct_1('#skF_4', '#skF_3')!=A_106 | k1_tarski(A_106)=k11_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_656, c_6])).
% 2.75/1.45  tff(c_683, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_672])).
% 2.75/1.45  tff(c_708, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_683])).
% 2.75/1.45  tff(c_709, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_708])).
% 2.75/1.45  tff(c_331, plain, (![A_62]: ('#skF_1'(A_62, k11_relat_1('#skF_4', '#skF_3'))=A_62 | r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3')) | k1_tarski(A_62)=k11_relat_1('#skF_4', '#skF_3') | '#skF_1'(A_62, k11_relat_1('#skF_4', '#skF_3'))=A_62 | k1_tarski(A_62)=k11_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_12])).
% 2.75/1.45  tff(c_641, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_331])).
% 2.75/1.45  tff(c_242, plain, (![A_1]: ('#skF_2'(A_1, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_1, k11_relat_1('#skF_4', '#skF_3'))=A_1 | k1_tarski(A_1)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_214])).
% 2.75/1.45  tff(c_716, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_242, c_709])).
% 2.75/1.45  tff(c_719, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_716])).
% 2.75/1.45  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.45  tff(c_240, plain, (![A_1]: ('#skF_2'(A_1, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_1'(A_1, k11_relat_1('#skF_4', '#skF_3')), k11_relat_1('#skF_4', '#skF_3')) | k1_tarski(A_1)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_214])).
% 2.75/1.45  tff(c_759, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3')) | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_719, c_240])).
% 2.75/1.45  tff(c_773, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_759])).
% 2.75/1.45  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_709, c_773])).
% 2.75/1.45  tff(c_777, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_331])).
% 2.75/1.45  tff(c_780, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_777])).
% 2.75/1.45  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_780])).
% 2.75/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  Inference rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Ref     : 0
% 2.75/1.45  #Sup     : 153
% 2.75/1.45  #Fact    : 2
% 2.75/1.45  #Define  : 0
% 2.75/1.45  #Split   : 2
% 2.75/1.45  #Chain   : 0
% 2.75/1.45  #Close   : 0
% 2.75/1.45  
% 2.75/1.45  Ordering : KBO
% 2.75/1.45  
% 2.75/1.45  Simplification rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Subsume      : 18
% 2.75/1.45  #Demod        : 20
% 2.75/1.45  #Tautology    : 31
% 2.75/1.45  #SimpNegUnit  : 5
% 2.75/1.45  #BackRed      : 0
% 2.75/1.45  
% 2.75/1.45  #Partial instantiations: 0
% 2.75/1.45  #Strategies tried      : 1
% 2.75/1.45  
% 2.75/1.45  Timing (in seconds)
% 2.75/1.45  ----------------------
% 2.75/1.45  Preprocessing        : 0.29
% 2.75/1.45  Parsing              : 0.15
% 2.75/1.45  CNF conversion       : 0.02
% 2.75/1.45  Main loop            : 0.38
% 2.75/1.45  Inferencing          : 0.15
% 2.75/1.45  Reduction            : 0.10
% 2.75/1.45  Demodulation         : 0.07
% 2.75/1.45  BG Simplification    : 0.02
% 2.75/1.45  Subsumption          : 0.09
% 2.75/1.45  Abstraction          : 0.03
% 2.75/1.46  MUC search           : 0.00
% 2.75/1.46  Cooper               : 0.00
% 2.75/1.46  Total                : 0.70
% 2.75/1.46  Index Insertion      : 0.00
% 2.75/1.46  Index Deletion       : 0.00
% 2.75/1.46  Index Matching       : 0.00
% 2.75/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
