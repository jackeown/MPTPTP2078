%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 111 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_50,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_28,plain,(
    ! [A_18] : v1_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_28])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_2'(A_35,B_36),k1_relat_1(B_36))
      | v5_funct_1(B_36,A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_35)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_97,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_95])).

tff(c_99,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_2'(A_37,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_95])).

tff(c_10,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,B_28)
      | ~ r2_hidden(C_29,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [C_29,A_6] :
      ( ~ r2_hidden(C_29,k1_xboole_0)
      | ~ r2_hidden(C_29,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_103,plain,(
    ! [A_38,A_39] :
      ( ~ r2_hidden('#skF_2'(A_38,k1_xboole_0),A_39)
      | v5_funct_1(k1_xboole_0,A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_99,c_65])).

tff(c_115,plain,(
    ! [A_40] :
      ( v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_97,c_103])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_30])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.21  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.99/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.21  
% 2.15/1.22  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.15/1.22  tff(f_50, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.15/1.22  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.15/1.22  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.15/1.22  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.15/1.22  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.15/1.22  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.15/1.22  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.15/1.22  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.15/1.22  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.22  tff(c_26, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.22  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_26])).
% 2.15/1.22  tff(c_28, plain, (![A_18]: (v1_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.22  tff(c_46, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_28])).
% 2.15/1.22  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.22  tff(c_92, plain, (![A_35, B_36]: (r2_hidden('#skF_2'(A_35, B_36), k1_relat_1(B_36)) | v5_funct_1(B_36, A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.22  tff(c_95, plain, (![A_35]: (r2_hidden('#skF_2'(A_35, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_35) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_14, c_92])).
% 2.15/1.22  tff(c_97, plain, (![A_35]: (r2_hidden('#skF_2'(A_35, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_95])).
% 2.15/1.22  tff(c_99, plain, (![A_37]: (r2_hidden('#skF_2'(A_37, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_95])).
% 2.15/1.22  tff(c_10, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.22  tff(c_62, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, B_28) | ~r2_hidden(C_29, A_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.15/1.22  tff(c_65, plain, (![C_29, A_6]: (~r2_hidden(C_29, k1_xboole_0) | ~r2_hidden(C_29, A_6))), inference(resolution, [status(thm)], [c_10, c_62])).
% 2.15/1.22  tff(c_103, plain, (![A_38, A_39]: (~r2_hidden('#skF_2'(A_38, k1_xboole_0), A_39) | v5_funct_1(k1_xboole_0, A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_99, c_65])).
% 2.15/1.22  tff(c_115, plain, (![A_40]: (v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_97, c_103])).
% 2.15/1.22  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.15/1.22  tff(c_118, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_30])).
% 2.15/1.22  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_118])).
% 2.15/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.22  
% 2.15/1.22  Inference rules
% 2.15/1.22  ----------------------
% 2.15/1.22  #Ref     : 0
% 2.15/1.22  #Sup     : 20
% 2.15/1.22  #Fact    : 0
% 2.15/1.22  #Define  : 0
% 2.15/1.22  #Split   : 0
% 2.15/1.22  #Chain   : 0
% 2.15/1.22  #Close   : 0
% 2.15/1.22  
% 2.15/1.22  Ordering : KBO
% 2.15/1.22  
% 2.15/1.22  Simplification rules
% 2.15/1.22  ----------------------
% 2.15/1.22  #Subsume      : 3
% 2.15/1.22  #Demod        : 10
% 2.15/1.22  #Tautology    : 10
% 2.15/1.22  #SimpNegUnit  : 0
% 2.15/1.22  #BackRed      : 0
% 2.15/1.22  
% 2.15/1.22  #Partial instantiations: 0
% 2.15/1.22  #Strategies tried      : 1
% 2.15/1.22  
% 2.15/1.22  Timing (in seconds)
% 2.15/1.22  ----------------------
% 2.15/1.23  Preprocessing        : 0.25
% 2.15/1.23  Parsing              : 0.14
% 2.15/1.23  CNF conversion       : 0.02
% 2.15/1.23  Main loop            : 0.15
% 2.15/1.23  Inferencing          : 0.06
% 2.15/1.23  Reduction            : 0.04
% 2.15/1.23  Demodulation         : 0.03
% 2.15/1.23  BG Simplification    : 0.01
% 2.15/1.23  Subsumption          : 0.02
% 2.15/1.23  Abstraction          : 0.01
% 2.15/1.23  MUC search           : 0.00
% 2.15/1.23  Cooper               : 0.00
% 2.15/1.23  Total                : 0.43
% 2.15/1.23  Index Insertion      : 0.00
% 2.15/1.23  Index Deletion       : 0.00
% 2.15/1.23  Index Matching       : 0.00
% 2.15/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
