%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 161 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 491 expanded)
%              Number of equality atoms :   22 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_51,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_4,B_7] :
      ( k1_funct_1(A_4,B_7) = k1_xboole_0
      | r2_hidden(B_7,k1_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k1_relat_1(k7_relat_1(C_3,B_2)))
      | ~ r2_hidden(A_1,k1_relat_1(C_3))
      | ~ r2_hidden(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [C_34,B_35,A_36] :
      ( k1_funct_1(k7_relat_1(C_34,B_35),A_36) = k1_funct_1(C_34,A_36)
      | ~ r2_hidden(A_36,k1_relat_1(k7_relat_1(C_34,B_35)))
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,(
    ! [C_43,B_44,A_45] :
      ( k1_funct_1(k7_relat_1(C_43,B_44),A_45) = k1_funct_1(C_43,A_45)
      | ~ v1_funct_1(C_43)
      | ~ r2_hidden(A_45,k1_relat_1(C_43))
      | ~ r2_hidden(A_45,B_44)
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_131,plain,(
    ! [A_49,B_50,B_51] :
      ( k1_funct_1(k7_relat_1(A_49,B_50),B_51) = k1_funct_1(A_49,B_51)
      | ~ r2_hidden(B_51,B_50)
      | k1_funct_1(A_49,B_51) = k1_xboole_0
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_22,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k1_funct_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_22])).

tff(c_153,plain,(
    k1_funct_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_143])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_funct_1(k7_relat_1(A_9,B_10))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,k1_relat_1(C_24))
      | ~ r2_hidden(A_23,k1_relat_1(k7_relat_1(C_24,B_25)))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [B_52,C_53,B_54] :
      ( r2_hidden(B_52,k1_relat_1(C_53))
      | ~ v1_relat_1(C_53)
      | k1_funct_1(k7_relat_1(C_53,B_54),B_52) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(C_53,B_54))
      | ~ v1_relat_1(k7_relat_1(C_53,B_54)) ) ),
    inference(resolution,[status(thm)],[c_14,c_38])).

tff(c_187,plain,(
    ! [B_55,A_56,B_57] :
      ( r2_hidden(B_55,k1_relat_1(A_56))
      | k1_funct_1(k7_relat_1(A_56,B_57),B_55) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_56,B_57))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_18,c_183])).

tff(c_191,plain,(
    ! [B_58,A_59,B_60] :
      ( r2_hidden(B_58,k1_relat_1(A_59))
      | k1_funct_1(k7_relat_1(A_59,B_60),B_58) = k1_xboole_0
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_10,plain,(
    ! [B_7,A_4] :
      ( r2_hidden(k4_tarski(B_7,k1_funct_1(A_4,B_7)),A_4)
      | ~ r2_hidden(B_7,k1_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,
    ( r2_hidden(k4_tarski('#skF_1',k1_xboole_0),'#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_10])).

tff(c_163,plain,
    ( r2_hidden(k4_tarski('#skF_1',k1_xboole_0),'#skF_3')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_159])).

tff(c_176,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_194,plain,(
    ! [B_60] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_60),'#skF_1') = k1_xboole_0
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_191,c_176])).

tff(c_237,plain,(
    ! [B_60] : k1_funct_1(k7_relat_1('#skF_3',B_60),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_194])).

tff(c_155,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_22])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_155])).

tff(c_255,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_92,plain,(
    ! [C_3,B_2,A_1] :
      ( k1_funct_1(k7_relat_1(C_3,B_2),A_1) = k1_funct_1(C_3,A_1)
      | ~ v1_funct_1(C_3)
      | ~ r2_hidden(A_1,k1_relat_1(C_3))
      | ~ r2_hidden(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_257,plain,(
    ! [B_2] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_2),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden('#skF_1',B_2)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_255,c_92])).

tff(c_267,plain,(
    ! [B_64] :
      ( k1_funct_1(k7_relat_1('#skF_3',B_64),'#skF_1') = k1_xboole_0
      | ~ r2_hidden('#skF_1',B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_153,c_257])).

tff(c_273,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_155])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.08/1.28  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.08/1.28  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.08/1.28  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.08/1.28  tff(f_59, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.08/1.28  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.28  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.28  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.28  tff(c_14, plain, (![A_4, B_7]: (k1_funct_1(A_4, B_7)=k1_xboole_0 | r2_hidden(B_7, k1_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k1_relat_1(k7_relat_1(C_3, B_2))) | ~r2_hidden(A_1, k1_relat_1(C_3)) | ~r2_hidden(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.28  tff(c_80, plain, (![C_34, B_35, A_36]: (k1_funct_1(k7_relat_1(C_34, B_35), A_36)=k1_funct_1(C_34, A_36) | ~r2_hidden(A_36, k1_relat_1(k7_relat_1(C_34, B_35))) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.28  tff(c_103, plain, (![C_43, B_44, A_45]: (k1_funct_1(k7_relat_1(C_43, B_44), A_45)=k1_funct_1(C_43, A_45) | ~v1_funct_1(C_43) | ~r2_hidden(A_45, k1_relat_1(C_43)) | ~r2_hidden(A_45, B_44) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.08/1.28  tff(c_131, plain, (![A_49, B_50, B_51]: (k1_funct_1(k7_relat_1(A_49, B_50), B_51)=k1_funct_1(A_49, B_51) | ~r2_hidden(B_51, B_50) | k1_funct_1(A_49, B_51)=k1_xboole_0 | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_14, c_103])).
% 2.08/1.28  tff(c_22, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.28  tff(c_143, plain, (~r2_hidden('#skF_1', '#skF_2') | k1_funct_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_22])).
% 2.08/1.28  tff(c_153, plain, (k1_funct_1('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_143])).
% 2.08/1.28  tff(c_16, plain, (![A_9, B_10]: (v1_funct_1(k7_relat_1(A_9, B_10)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.28  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.28  tff(c_38, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, k1_relat_1(C_24)) | ~r2_hidden(A_23, k1_relat_1(k7_relat_1(C_24, B_25))) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.28  tff(c_183, plain, (![B_52, C_53, B_54]: (r2_hidden(B_52, k1_relat_1(C_53)) | ~v1_relat_1(C_53) | k1_funct_1(k7_relat_1(C_53, B_54), B_52)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(C_53, B_54)) | ~v1_relat_1(k7_relat_1(C_53, B_54)))), inference(resolution, [status(thm)], [c_14, c_38])).
% 2.08/1.28  tff(c_187, plain, (![B_55, A_56, B_57]: (r2_hidden(B_55, k1_relat_1(A_56)) | k1_funct_1(k7_relat_1(A_56, B_57), B_55)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(A_56, B_57)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_18, c_183])).
% 2.08/1.28  tff(c_191, plain, (![B_58, A_59, B_60]: (r2_hidden(B_58, k1_relat_1(A_59)) | k1_funct_1(k7_relat_1(A_59, B_60), B_58)=k1_xboole_0 | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_16, c_187])).
% 2.08/1.28  tff(c_10, plain, (![B_7, A_4]: (r2_hidden(k4_tarski(B_7, k1_funct_1(A_4, B_7)), A_4) | ~r2_hidden(B_7, k1_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_159, plain, (r2_hidden(k4_tarski('#skF_1', k1_xboole_0), '#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_153, c_10])).
% 2.08/1.28  tff(c_163, plain, (r2_hidden(k4_tarski('#skF_1', k1_xboole_0), '#skF_3') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_159])).
% 2.08/1.28  tff(c_176, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_163])).
% 2.08/1.28  tff(c_194, plain, (![B_60]: (k1_funct_1(k7_relat_1('#skF_3', B_60), '#skF_1')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_191, c_176])).
% 2.08/1.28  tff(c_237, plain, (![B_60]: (k1_funct_1(k7_relat_1('#skF_3', B_60), '#skF_1')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_194])).
% 2.08/1.28  tff(c_155, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_153, c_22])).
% 2.08/1.28  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_155])).
% 2.08/1.28  tff(c_255, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_163])).
% 2.08/1.28  tff(c_92, plain, (![C_3, B_2, A_1]: (k1_funct_1(k7_relat_1(C_3, B_2), A_1)=k1_funct_1(C_3, A_1) | ~v1_funct_1(C_3) | ~r2_hidden(A_1, k1_relat_1(C_3)) | ~r2_hidden(A_1, B_2) | ~v1_relat_1(C_3))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.08/1.28  tff(c_257, plain, (![B_2]: (k1_funct_1(k7_relat_1('#skF_3', B_2), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~r2_hidden('#skF_1', B_2) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_255, c_92])).
% 2.08/1.28  tff(c_267, plain, (![B_64]: (k1_funct_1(k7_relat_1('#skF_3', B_64), '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', B_64))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_153, c_257])).
% 2.08/1.28  tff(c_273, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_267, c_155])).
% 2.08/1.28  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_273])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 59
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 1
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 7
% 2.08/1.28  #Demod        : 31
% 2.08/1.28  #Tautology    : 21
% 2.08/1.28  #SimpNegUnit  : 0
% 2.08/1.28  #BackRed      : 2
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.28
% 2.08/1.28  Parsing              : 0.15
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.24
% 2.08/1.29  Inferencing          : 0.10
% 2.08/1.29  Reduction            : 0.06
% 2.08/1.29  Demodulation         : 0.04
% 2.08/1.29  BG Simplification    : 0.01
% 2.08/1.29  Subsumption          : 0.05
% 2.08/1.29  Abstraction          : 0.01
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.55
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
