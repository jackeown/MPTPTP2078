%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:43 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 142 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
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

tff(c_20,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_relat_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_23,C_24,B_25] :
      ( ~ r2_hidden(A_23,C_24)
      | ~ r1_xboole_0(k2_tarski(A_23,B_25),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_23] : ~ r2_hidden(A_23,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_53,plain,(
    ! [A_28] :
      ( v1_xboole_0(k1_funct_1(A_28,'#skF_1'(A_28)))
      | v2_relat_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_28] :
      ( k1_funct_1(A_28,'#skF_1'(A_28)) = k1_xboole_0
      | v2_relat_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_127,plain,(
    ! [B_42,C_43,A_44] :
      ( r2_hidden(k1_funct_1(B_42,C_43),k1_funct_1(A_44,C_43))
      | ~ r2_hidden(C_43,k1_relat_1(B_42))
      | ~ v5_funct_1(B_42,A_44)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [B_42,A_28] :
      ( r2_hidden(k1_funct_1(B_42,'#skF_1'(A_28)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_28),k1_relat_1(B_42))
      | ~ v5_funct_1(B_42,A_28)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28)
      | v2_relat_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_127])).

tff(c_140,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45),k1_relat_1(B_46))
      | ~ v5_funct_1(B_46,A_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v2_relat_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_137])).

tff(c_146,plain,(
    ! [A_45] :
      ( ~ r2_hidden('#skF_1'(A_45),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_45)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45)
      | v2_relat_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_150,plain,(
    ! [A_47] :
      ( ~ r2_hidden('#skF_1'(A_47),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_47)
      | v2_relat_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_146])).

tff(c_154,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_157,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.33  
% 2.02/1.33  %Foreground sorts:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Background operators:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Foreground operators:
% 2.02/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.33  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.02/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.33  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.02/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.33  
% 2.02/1.34  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_1)).
% 2.02/1.34  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_funct_1)).
% 2.02/1.34  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.34  tff(f_36, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.02/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.34  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.02/1.34  tff(c_20, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_24, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_relat_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.34  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_22, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.34  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.34  tff(c_39, plain, (![A_23, C_24, B_25]: (~r2_hidden(A_23, C_24) | ~r1_xboole_0(k2_tarski(A_23, B_25), C_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.02/1.34  tff(c_44, plain, (![A_23]: (~r2_hidden(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_39])).
% 2.02/1.34  tff(c_53, plain, (![A_28]: (v1_xboole_0(k1_funct_1(A_28, '#skF_1'(A_28))) | v2_relat_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.34  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.34  tff(c_57, plain, (![A_28]: (k1_funct_1(A_28, '#skF_1'(A_28))=k1_xboole_0 | v2_relat_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.02/1.34  tff(c_127, plain, (![B_42, C_43, A_44]: (r2_hidden(k1_funct_1(B_42, C_43), k1_funct_1(A_44, C_43)) | ~r2_hidden(C_43, k1_relat_1(B_42)) | ~v5_funct_1(B_42, A_44) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.34  tff(c_137, plain, (![B_42, A_28]: (r2_hidden(k1_funct_1(B_42, '#skF_1'(A_28)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_28), k1_relat_1(B_42)) | ~v5_funct_1(B_42, A_28) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28) | v2_relat_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_57, c_127])).
% 2.02/1.34  tff(c_140, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45), k1_relat_1(B_46)) | ~v5_funct_1(B_46, A_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v2_relat_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(negUnitSimplification, [status(thm)], [c_44, c_137])).
% 2.02/1.34  tff(c_146, plain, (![A_45]: (~r2_hidden('#skF_1'(A_45), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_45) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_45) | ~v1_relat_1(A_45) | v2_relat_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 2.02/1.34  tff(c_150, plain, (![A_47]: (~r2_hidden('#skF_1'(A_47), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_47) | v2_relat_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_146])).
% 2.02/1.34  tff(c_154, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_150])).
% 2.02/1.34  tff(c_157, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_154])).
% 2.02/1.34  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_157])).
% 2.02/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  Inference rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Ref     : 0
% 2.02/1.34  #Sup     : 23
% 2.02/1.34  #Fact    : 0
% 2.02/1.34  #Define  : 0
% 2.02/1.34  #Split   : 2
% 2.02/1.34  #Chain   : 0
% 2.02/1.34  #Close   : 0
% 2.02/1.34  
% 2.02/1.34  Ordering : KBO
% 2.02/1.34  
% 2.02/1.34  Simplification rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Subsume      : 1
% 2.02/1.34  #Demod        : 18
% 2.02/1.34  #Tautology    : 7
% 2.02/1.34  #SimpNegUnit  : 3
% 2.02/1.34  #BackRed      : 0
% 2.02/1.34  
% 2.02/1.34  #Partial instantiations: 0
% 2.02/1.34  #Strategies tried      : 1
% 2.02/1.34  
% 2.02/1.34  Timing (in seconds)
% 2.02/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.30
% 2.26/1.34  Parsing              : 0.17
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.18
% 2.26/1.34  Inferencing          : 0.08
% 2.26/1.34  Reduction            : 0.05
% 2.26/1.35  Demodulation         : 0.03
% 2.26/1.35  BG Simplification    : 0.02
% 2.26/1.35  Subsumption          : 0.03
% 2.26/1.35  Abstraction          : 0.01
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.50
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
