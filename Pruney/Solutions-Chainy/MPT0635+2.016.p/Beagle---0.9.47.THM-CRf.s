%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  96 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_38,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ! [D_22,B_23,A_24] :
      ( r2_hidden(D_22,B_23)
      | ~ r2_hidden(D_22,k3_xboole_0(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( k1_funct_1(k6_relat_1(B_18),A_17) = A_17
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_12] :
      ( k1_relat_1(k6_relat_1(A_12)) = A_12
      | ~ v1_funct_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_12] :
      ( k1_relat_1(k6_relat_1(A_12)) = A_12
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32])).

tff(c_46,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_413,plain,(
    ! [B_75,C_76,A_77] :
      ( k1_funct_1(k5_relat_1(B_75,C_76),A_77) = k1_funct_1(C_76,k1_funct_1(B_75,A_77))
      | ~ r2_hidden(A_77,k1_relat_1(B_75))
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_455,plain,(
    ! [A_12,C_76,A_77] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_12),C_76),A_77) = k1_funct_1(C_76,k1_funct_1(k6_relat_1(A_12),A_77))
      | ~ r2_hidden(A_77,A_12)
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_funct_1(k6_relat_1(A_12))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_413])).

tff(c_483,plain,(
    ! [A_79,C_80,A_81] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_79),C_80),A_81) = k1_funct_1(C_80,k1_funct_1(k6_relat_1(A_79),A_81))
      | ~ r2_hidden(A_81,A_79)
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_455])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_493,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_36])).

tff(c_499,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62,c_493])).

tff(c_503,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_499])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:30:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.54/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.36  
% 2.54/1.37  tff(f_77, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 2.54/1.37  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.54/1.37  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 2.54/1.37  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.54/1.37  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.54/1.37  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.54/1.37  tff(c_38, plain, (r2_hidden('#skF_4', k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.37  tff(c_58, plain, (![D_22, B_23, A_24]: (r2_hidden(D_22, B_23) | ~r2_hidden(D_22, k3_xboole_0(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.54/1.37  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.54/1.37  tff(c_34, plain, (![B_18, A_17]: (k1_funct_1(k6_relat_1(B_18), A_17)=A_17 | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.37  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.37  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.37  tff(c_20, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.37  tff(c_22, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.37  tff(c_32, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12 | ~v1_funct_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.54/1.37  tff(c_44, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12 | ~v1_relat_1(k6_relat_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32])).
% 2.54/1.37  tff(c_46, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_44])).
% 2.54/1.37  tff(c_413, plain, (![B_75, C_76, A_77]: (k1_funct_1(k5_relat_1(B_75, C_76), A_77)=k1_funct_1(C_76, k1_funct_1(B_75, A_77)) | ~r2_hidden(A_77, k1_relat_1(B_75)) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.37  tff(c_455, plain, (![A_12, C_76, A_77]: (k1_funct_1(k5_relat_1(k6_relat_1(A_12), C_76), A_77)=k1_funct_1(C_76, k1_funct_1(k6_relat_1(A_12), A_77)) | ~r2_hidden(A_77, A_12) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76) | ~v1_funct_1(k6_relat_1(A_12)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_413])).
% 2.54/1.37  tff(c_483, plain, (![A_79, C_80, A_81]: (k1_funct_1(k5_relat_1(k6_relat_1(A_79), C_80), A_81)=k1_funct_1(C_80, k1_funct_1(k6_relat_1(A_79), A_81)) | ~r2_hidden(A_81, A_79) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_455])).
% 2.54/1.37  tff(c_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.54/1.37  tff(c_493, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_483, c_36])).
% 2.54/1.37  tff(c_499, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62, c_493])).
% 2.54/1.37  tff(c_503, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_499])).
% 2.54/1.37  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_503])).
% 2.54/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  Inference rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Ref     : 0
% 2.54/1.37  #Sup     : 96
% 2.54/1.37  #Fact    : 0
% 2.54/1.37  #Define  : 0
% 2.54/1.37  #Split   : 0
% 2.54/1.37  #Chain   : 0
% 2.54/1.37  #Close   : 0
% 2.54/1.37  
% 2.54/1.37  Ordering : KBO
% 2.54/1.37  
% 2.54/1.37  Simplification rules
% 2.54/1.37  ----------------------
% 2.54/1.37  #Subsume      : 14
% 2.54/1.37  #Demod        : 56
% 2.54/1.37  #Tautology    : 25
% 2.54/1.37  #SimpNegUnit  : 0
% 2.54/1.37  #BackRed      : 0
% 2.54/1.37  
% 2.54/1.37  #Partial instantiations: 0
% 2.54/1.37  #Strategies tried      : 1
% 2.54/1.37  
% 2.54/1.37  Timing (in seconds)
% 2.54/1.37  ----------------------
% 2.54/1.37  Preprocessing        : 0.29
% 2.54/1.37  Parsing              : 0.16
% 2.54/1.37  CNF conversion       : 0.02
% 2.54/1.37  Main loop            : 0.32
% 2.54/1.37  Inferencing          : 0.13
% 2.54/1.37  Reduction            : 0.08
% 2.54/1.37  Demodulation         : 0.06
% 2.54/1.37  BG Simplification    : 0.02
% 2.54/1.37  Subsumption          : 0.07
% 2.54/1.37  Abstraction          : 0.02
% 2.54/1.37  MUC search           : 0.00
% 2.54/1.37  Cooper               : 0.00
% 2.54/1.37  Total                : 0.64
% 2.54/1.37  Index Insertion      : 0.00
% 2.54/1.37  Index Deletion       : 0.00
% 2.54/1.37  Index Matching       : 0.00
% 2.54/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
