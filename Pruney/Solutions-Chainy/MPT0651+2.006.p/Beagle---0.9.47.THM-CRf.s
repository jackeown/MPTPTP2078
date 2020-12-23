%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:48 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   47 (  93 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 246 expanded)
%              Number of equality atoms :   25 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ! [A_16] :
      ( k4_relat_1(A_16) = k2_funct_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_43,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_40])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_8])).

tff(c_51,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_143,plain,(
    ! [B_28,A_29] :
      ( k2_relat_1(k5_relat_1(B_28,A_29)) = k2_relat_1(A_29)
      | ~ r1_tarski(k1_relat_1(A_29),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_248,plain,(
    ! [B_38,A_39] :
      ( k2_relat_1(k5_relat_1(B_38,k2_funct_1(A_39))) = k2_relat_1(k2_funct_1(A_39))
      | ~ r1_tarski(k2_relat_1(A_39),k2_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_143])).

tff(c_266,plain,(
    ! [A_40] :
      ( k2_relat_1(k5_relat_1(A_40,k2_funct_1(A_40))) = k2_relat_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_248])).

tff(c_72,plain,(
    ! [A_19,B_20] :
      ( k1_relat_1(k5_relat_1(A_19,B_20)) = k1_relat_1(A_19)
      | ~ r1_tarski(k2_relat_1(A_19),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [A_23,A_24] :
      ( k1_relat_1(k5_relat_1(A_23,k2_funct_1(A_24))) = k1_relat_1(A_23)
      | ~ r1_tarski(k2_relat_1(A_23),k2_relat_1(A_24))
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v1_relat_1(A_23)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_72])).

tff(c_98,plain,(
    ! [A_25] :
      ( k1_relat_1(k5_relat_1(A_25,k2_funct_1(A_25))) = k1_relat_1(A_25)
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_110,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_53])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_51,c_110])).

tff(c_119,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_290,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_119])).

tff(c_296,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_51,c_290])).

tff(c_300,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_296])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  
% 2.26/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.36  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.26/1.36  
% 2.26/1.36  %Foreground sorts:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Background operators:
% 2.26/1.36  
% 2.26/1.36  
% 2.26/1.36  %Foreground operators:
% 2.26/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.26/1.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.26/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.26/1.36  
% 2.26/1.37  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.26/1.37  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.26/1.37  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.26/1.37  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.26/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.37  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.26/1.37  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.26/1.37  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.37  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.37  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.37  tff(c_16, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.37  tff(c_37, plain, (![A_16]: (k4_relat_1(A_16)=k2_funct_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.37  tff(c_40, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.26/1.37  tff(c_43, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_40])).
% 2.26/1.37  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.37  tff(c_47, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_8])).
% 2.26/1.37  tff(c_51, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_47])).
% 2.26/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.37  tff(c_18, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.37  tff(c_143, plain, (![B_28, A_29]: (k2_relat_1(k5_relat_1(B_28, A_29))=k2_relat_1(A_29) | ~r1_tarski(k1_relat_1(A_29), k2_relat_1(B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.37  tff(c_248, plain, (![B_38, A_39]: (k2_relat_1(k5_relat_1(B_38, k2_funct_1(A_39)))=k2_relat_1(k2_funct_1(A_39)) | ~r1_tarski(k2_relat_1(A_39), k2_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_18, c_143])).
% 2.26/1.37  tff(c_266, plain, (![A_40]: (k2_relat_1(k5_relat_1(A_40, k2_funct_1(A_40)))=k2_relat_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_6, c_248])).
% 2.26/1.37  tff(c_72, plain, (![A_19, B_20]: (k1_relat_1(k5_relat_1(A_19, B_20))=k1_relat_1(A_19) | ~r1_tarski(k2_relat_1(A_19), k1_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.37  tff(c_86, plain, (![A_23, A_24]: (k1_relat_1(k5_relat_1(A_23, k2_funct_1(A_24)))=k1_relat_1(A_23) | ~r1_tarski(k2_relat_1(A_23), k2_relat_1(A_24)) | ~v1_relat_1(k2_funct_1(A_24)) | ~v1_relat_1(A_23) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_18, c_72])).
% 2.26/1.37  tff(c_98, plain, (![A_25]: (k1_relat_1(k5_relat_1(A_25, k2_funct_1(A_25)))=k1_relat_1(A_25) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.26/1.37  tff(c_20, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.37  tff(c_53, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.26/1.37  tff(c_110, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_98, c_53])).
% 2.26/1.37  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_51, c_110])).
% 2.26/1.37  tff(c_119, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.26/1.37  tff(c_290, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_119])).
% 2.26/1.37  tff(c_296, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_51, c_290])).
% 2.26/1.37  tff(c_300, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_296])).
% 2.26/1.37  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_300])).
% 2.26/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.37  
% 2.26/1.37  Inference rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Ref     : 0
% 2.26/1.37  #Sup     : 70
% 2.26/1.37  #Fact    : 0
% 2.26/1.37  #Define  : 0
% 2.26/1.37  #Split   : 2
% 2.26/1.37  #Chain   : 0
% 2.26/1.37  #Close   : 0
% 2.26/1.37  
% 2.26/1.37  Ordering : KBO
% 2.26/1.37  
% 2.26/1.37  Simplification rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Subsume      : 3
% 2.26/1.37  #Demod        : 24
% 2.26/1.37  #Tautology    : 23
% 2.26/1.37  #SimpNegUnit  : 0
% 2.26/1.37  #BackRed      : 0
% 2.26/1.37  
% 2.26/1.37  #Partial instantiations: 0
% 2.26/1.37  #Strategies tried      : 1
% 2.26/1.37  
% 2.26/1.37  Timing (in seconds)
% 2.26/1.37  ----------------------
% 2.26/1.38  Preprocessing        : 0.32
% 2.26/1.38  Parsing              : 0.17
% 2.26/1.38  CNF conversion       : 0.02
% 2.26/1.38  Main loop            : 0.23
% 2.26/1.38  Inferencing          : 0.09
% 2.26/1.38  Reduction            : 0.06
% 2.26/1.38  Demodulation         : 0.05
% 2.26/1.38  BG Simplification    : 0.02
% 2.26/1.38  Subsumption          : 0.05
% 2.26/1.38  Abstraction          : 0.01
% 2.26/1.38  MUC search           : 0.00
% 2.26/1.38  Cooper               : 0.00
% 2.26/1.38  Total                : 0.58
% 2.26/1.38  Index Insertion      : 0.00
% 2.26/1.38  Index Deletion       : 0.00
% 2.26/1.38  Index Matching       : 0.00
% 2.26/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
