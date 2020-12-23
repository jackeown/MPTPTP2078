%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  81 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
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

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    ! [A_7,C_38] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_143])).

tff(c_148,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_146])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_45,plain,(
    ! [A_27] :
      ( v1_funct_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_57,plain,(
    ! [A_29] :
      ( v1_xboole_0(k1_relat_1(A_29))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = k1_xboole_0
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_79,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_159,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),k1_relat_1(B_43))
      | v5_funct_1(B_43,A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_165,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_159])).

tff(c_168,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_49,c_165])).

tff(c_170,plain,(
    ! [A_44] :
      ( v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_168])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_173,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_28])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.09  
% 1.82/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.09  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.82/1.09  
% 1.82/1.09  %Foreground sorts:
% 1.82/1.09  
% 1.82/1.09  
% 1.82/1.09  %Background operators:
% 1.82/1.09  
% 1.82/1.09  
% 1.82/1.09  %Foreground operators:
% 1.82/1.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.09  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.82/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.82/1.09  
% 1.82/1.10  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.82/1.10  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.82/1.10  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.82/1.10  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.82/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.82/1.10  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.82/1.10  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.82/1.10  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.82/1.10  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.82/1.10  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.82/1.10  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.10  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.10  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.10  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.10  tff(c_143, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.10  tff(c_146, plain, (![A_7, C_38]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_143])).
% 1.82/1.10  tff(c_148, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_146])).
% 1.82/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.82/1.10  tff(c_34, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.10  tff(c_38, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.82/1.10  tff(c_45, plain, (![A_27]: (v1_funct_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.10  tff(c_49, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.82/1.10  tff(c_57, plain, (![A_29]: (v1_xboole_0(k1_relat_1(A_29)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.82/1.10  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.82/1.10  tff(c_71, plain, (![A_31]: (k1_relat_1(A_31)=k1_xboole_0 | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_57, c_4])).
% 1.82/1.10  tff(c_79, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_71])).
% 1.82/1.10  tff(c_159, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), k1_relat_1(B_43)) | v5_funct_1(B_43, A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.82/1.10  tff(c_165, plain, (![A_42]: (r2_hidden('#skF_2'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_79, c_159])).
% 1.82/1.10  tff(c_168, plain, (![A_42]: (r2_hidden('#skF_2'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_49, c_165])).
% 1.82/1.10  tff(c_170, plain, (![A_44]: (v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(negUnitSimplification, [status(thm)], [c_148, c_168])).
% 1.82/1.10  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.10  tff(c_173, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_170, c_28])).
% 1.82/1.10  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_173])).
% 1.82/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.10  
% 1.82/1.10  Inference rules
% 1.82/1.10  ----------------------
% 1.82/1.10  #Ref     : 0
% 1.82/1.10  #Sup     : 31
% 1.82/1.10  #Fact    : 0
% 1.82/1.10  #Define  : 0
% 1.82/1.10  #Split   : 0
% 1.82/1.10  #Chain   : 0
% 1.82/1.10  #Close   : 0
% 1.82/1.10  
% 1.82/1.10  Ordering : KBO
% 1.82/1.10  
% 1.82/1.10  Simplification rules
% 1.82/1.10  ----------------------
% 1.82/1.10  #Subsume      : 0
% 1.82/1.10  #Demod        : 19
% 1.82/1.10  #Tautology    : 20
% 1.82/1.10  #SimpNegUnit  : 2
% 1.82/1.10  #BackRed      : 0
% 1.82/1.10  
% 1.82/1.10  #Partial instantiations: 0
% 1.82/1.10  #Strategies tried      : 1
% 1.82/1.10  
% 1.82/1.10  Timing (in seconds)
% 1.82/1.10  ----------------------
% 1.82/1.11  Preprocessing        : 0.27
% 1.82/1.11  Parsing              : 0.15
% 1.82/1.11  CNF conversion       : 0.02
% 1.82/1.11  Main loop            : 0.14
% 1.82/1.11  Inferencing          : 0.06
% 1.82/1.11  Reduction            : 0.04
% 1.82/1.11  Demodulation         : 0.03
% 1.82/1.11  BG Simplification    : 0.01
% 1.82/1.11  Subsumption          : 0.02
% 1.82/1.11  Abstraction          : 0.01
% 1.82/1.11  MUC search           : 0.00
% 1.82/1.11  Cooper               : 0.00
% 1.82/1.11  Total                : 0.43
% 1.82/1.11  Index Insertion      : 0.00
% 1.82/1.11  Index Deletion       : 0.00
% 1.82/1.11  Index Matching       : 0.00
% 1.82/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
