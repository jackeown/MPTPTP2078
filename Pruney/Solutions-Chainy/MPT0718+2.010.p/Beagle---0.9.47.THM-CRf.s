%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:43 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 142 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
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

tff(c_28,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),k1_relat_1(A_11))
      | v2_relat_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | k4_xboole_0(A_34,k1_tarski(B_33)) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [B_33] : ~ r2_hidden(B_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_110,plain,(
    ! [A_39] :
      ( v1_xboole_0(k1_funct_1(A_39,'#skF_1'(A_39)))
      | v2_relat_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [A_39] :
      ( k1_funct_1(A_39,'#skF_1'(A_39)) = k1_xboole_0
      | v2_relat_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_189,plain,(
    ! [B_50,C_51,A_52] :
      ( r2_hidden(k1_funct_1(B_50,C_51),k1_funct_1(A_52,C_51))
      | ~ r2_hidden(C_51,k1_relat_1(B_50))
      | ~ v5_funct_1(B_50,A_52)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_195,plain,(
    ! [B_50,A_39] :
      ( r2_hidden(k1_funct_1(B_50,'#skF_1'(A_39)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_39),k1_relat_1(B_50))
      | ~ v5_funct_1(B_50,A_39)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | v2_relat_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_189])).

tff(c_204,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57),k1_relat_1(B_58))
      | ~ v5_funct_1(B_58,A_57)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57)
      | v2_relat_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_195])).

tff(c_210,plain,(
    ! [A_57] :
      ( ~ r2_hidden('#skF_1'(A_57),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_57)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57)
      | v2_relat_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_204])).

tff(c_215,plain,(
    ! [A_60] :
      ( ~ r2_hidden('#skF_1'(A_60),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_60)
      | v2_relat_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_210])).

tff(c_219,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_215])).

tff(c_222,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_219])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  %$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.29  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.10/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.29  
% 2.10/1.30  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 2.10/1.30  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 2.10/1.30  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.10/1.30  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.10/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.10/1.30  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.10/1.30  tff(c_28, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_32, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_20, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), k1_relat_1(A_11)) | v2_relat_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.30  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_30, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.30  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.30  tff(c_90, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | k4_xboole_0(A_34, k1_tarski(B_33))!=A_34)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.30  tff(c_99, plain, (![B_33]: (~r2_hidden(B_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_90])).
% 2.10/1.30  tff(c_110, plain, (![A_39]: (v1_xboole_0(k1_funct_1(A_39, '#skF_1'(A_39))) | v2_relat_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.30  tff(c_114, plain, (![A_39]: (k1_funct_1(A_39, '#skF_1'(A_39))=k1_xboole_0 | v2_relat_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.10/1.30  tff(c_189, plain, (![B_50, C_51, A_52]: (r2_hidden(k1_funct_1(B_50, C_51), k1_funct_1(A_52, C_51)) | ~r2_hidden(C_51, k1_relat_1(B_50)) | ~v5_funct_1(B_50, A_52) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.30  tff(c_195, plain, (![B_50, A_39]: (r2_hidden(k1_funct_1(B_50, '#skF_1'(A_39)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_39), k1_relat_1(B_50)) | ~v5_funct_1(B_50, A_39) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | v2_relat_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_114, c_189])).
% 2.10/1.30  tff(c_204, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57), k1_relat_1(B_58)) | ~v5_funct_1(B_58, A_57) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57) | v2_relat_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(negUnitSimplification, [status(thm)], [c_99, c_195])).
% 2.10/1.30  tff(c_210, plain, (![A_57]: (~r2_hidden('#skF_1'(A_57), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_57) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_57) | ~v1_relat_1(A_57) | v2_relat_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_30, c_204])).
% 2.10/1.30  tff(c_215, plain, (![A_60]: (~r2_hidden('#skF_1'(A_60), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_60) | v2_relat_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_210])).
% 2.10/1.30  tff(c_219, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_215])).
% 2.10/1.30  tff(c_222, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_219])).
% 2.10/1.30  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_222])).
% 2.10/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  Inference rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Ref     : 0
% 2.10/1.30  #Sup     : 36
% 2.10/1.30  #Fact    : 0
% 2.10/1.30  #Define  : 0
% 2.10/1.30  #Split   : 2
% 2.10/1.30  #Chain   : 0
% 2.10/1.30  #Close   : 0
% 2.10/1.30  
% 2.10/1.30  Ordering : KBO
% 2.10/1.30  
% 2.10/1.30  Simplification rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Subsume      : 1
% 2.10/1.30  #Demod        : 18
% 2.10/1.30  #Tautology    : 20
% 2.10/1.30  #SimpNegUnit  : 3
% 2.10/1.30  #BackRed      : 0
% 2.10/1.30  
% 2.10/1.30  #Partial instantiations: 0
% 2.10/1.30  #Strategies tried      : 1
% 2.10/1.30  
% 2.10/1.30  Timing (in seconds)
% 2.10/1.30  ----------------------
% 2.10/1.31  Preprocessing        : 0.32
% 2.10/1.31  Parsing              : 0.17
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.19
% 2.10/1.31  Inferencing          : 0.08
% 2.10/1.31  Reduction            : 0.06
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.03
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.54
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
