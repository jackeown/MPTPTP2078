%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
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
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

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
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),k1_relat_1(A_5))
      | v2_relat_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
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
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | ~ r1_xboole_0(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_53,plain,(
    ! [A_26] :
      ( v1_xboole_0(k1_funct_1(A_26,'#skF_1'(A_26)))
      | v2_relat_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_26] :
      ( k1_funct_1(A_26,'#skF_1'(A_26)) = k1_xboole_0
      | v2_relat_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_127,plain,(
    ! [B_40,C_41,A_42] :
      ( r2_hidden(k1_funct_1(B_40,C_41),k1_funct_1(A_42,C_41))
      | ~ r2_hidden(C_41,k1_relat_1(B_40))
      | ~ v5_funct_1(B_40,A_42)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [B_40,A_26] :
      ( r2_hidden(k1_funct_1(B_40,'#skF_1'(A_26)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_26),k1_relat_1(B_40))
      | ~ v5_funct_1(B_40,A_26)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26)
      | v2_relat_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_127])).

tff(c_140,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43),k1_relat_1(B_44))
      | ~ v5_funct_1(B_44,A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43)
      | v2_relat_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_137])).

tff(c_146,plain,(
    ! [A_43] :
      ( ~ r2_hidden('#skF_1'(A_43),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_43)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43)
      | v2_relat_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_150,plain,(
    ! [A_45] :
      ( ~ r2_hidden('#skF_1'(A_45),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_45)
      | v2_relat_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
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
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  
% 1.91/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.91/1.31  
% 1.91/1.31  %Foreground sorts:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Background operators:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Foreground operators:
% 1.91/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.31  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 1.91/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.31  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.91/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.31  
% 1.91/1.32  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 1.91/1.32  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 1.91/1.32  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.32  tff(f_36, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.91/1.32  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.91/1.32  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.91/1.32  tff(c_20, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_24, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_12, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), k1_relat_1(A_5)) | v2_relat_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.32  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_22, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.32  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.32  tff(c_39, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | ~r1_xboole_0(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.32  tff(c_44, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_39])).
% 1.91/1.32  tff(c_53, plain, (![A_26]: (v1_xboole_0(k1_funct_1(A_26, '#skF_1'(A_26))) | v2_relat_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.32  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.32  tff(c_57, plain, (![A_26]: (k1_funct_1(A_26, '#skF_1'(A_26))=k1_xboole_0 | v2_relat_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_53, c_2])).
% 1.91/1.32  tff(c_127, plain, (![B_40, C_41, A_42]: (r2_hidden(k1_funct_1(B_40, C_41), k1_funct_1(A_42, C_41)) | ~r2_hidden(C_41, k1_relat_1(B_40)) | ~v5_funct_1(B_40, A_42) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.91/1.32  tff(c_137, plain, (![B_40, A_26]: (r2_hidden(k1_funct_1(B_40, '#skF_1'(A_26)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_26), k1_relat_1(B_40)) | ~v5_funct_1(B_40, A_26) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26) | v2_relat_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_57, c_127])).
% 1.91/1.32  tff(c_140, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43), k1_relat_1(B_44)) | ~v5_funct_1(B_44, A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43) | v2_relat_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(negUnitSimplification, [status(thm)], [c_44, c_137])).
% 1.91/1.32  tff(c_146, plain, (![A_43]: (~r2_hidden('#skF_1'(A_43), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_43) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_43) | ~v1_relat_1(A_43) | v2_relat_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 1.91/1.32  tff(c_150, plain, (![A_45]: (~r2_hidden('#skF_1'(A_45), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_45) | v2_relat_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_146])).
% 1.91/1.32  tff(c_154, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_150])).
% 1.91/1.32  tff(c_157, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_154])).
% 1.91/1.32  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_157])).
% 1.91/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.32  
% 1.91/1.32  Inference rules
% 1.91/1.32  ----------------------
% 1.91/1.32  #Ref     : 0
% 1.91/1.32  #Sup     : 23
% 1.91/1.32  #Fact    : 0
% 1.91/1.32  #Define  : 0
% 1.91/1.32  #Split   : 2
% 1.91/1.32  #Chain   : 0
% 1.91/1.32  #Close   : 0
% 1.91/1.32  
% 1.91/1.32  Ordering : KBO
% 1.91/1.32  
% 1.91/1.32  Simplification rules
% 1.91/1.32  ----------------------
% 1.91/1.32  #Subsume      : 1
% 1.91/1.32  #Demod        : 18
% 1.91/1.32  #Tautology    : 7
% 1.91/1.32  #SimpNegUnit  : 3
% 1.91/1.32  #BackRed      : 0
% 1.91/1.32  
% 1.91/1.32  #Partial instantiations: 0
% 1.91/1.32  #Strategies tried      : 1
% 1.91/1.32  
% 1.91/1.32  Timing (in seconds)
% 1.91/1.32  ----------------------
% 1.91/1.33  Preprocessing        : 0.32
% 1.91/1.33  Parsing              : 0.17
% 1.91/1.33  CNF conversion       : 0.02
% 1.91/1.33  Main loop            : 0.17
% 1.91/1.33  Inferencing          : 0.07
% 2.21/1.33  Reduction            : 0.05
% 2.21/1.33  Demodulation         : 0.04
% 2.21/1.33  BG Simplification    : 0.02
% 2.21/1.33  Subsumption          : 0.03
% 2.21/1.33  Abstraction          : 0.01
% 2.21/1.33  MUC search           : 0.00
% 2.21/1.33  Cooper               : 0.00
% 2.21/1.33  Total                : 0.52
% 2.21/1.33  Index Insertion      : 0.00
% 2.21/1.33  Index Deletion       : 0.00
% 2.21/1.33  Index Matching       : 0.00
% 2.21/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
