%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:24 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  88 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_38,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_125,plain,(
    ! [A_77] :
      ( k2_xboole_0(k1_relat_1(A_77),k2_relat_1(A_77)) = k3_relat_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_134,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_140,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8,c_134])).

tff(c_141,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_140])).

tff(c_104,plain,(
    ! [A_76] :
      ( k2_xboole_0(k1_relat_1(A_76),k2_relat_1(A_76)) = k3_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_113,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_104])).

tff(c_119,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36,c_113])).

tff(c_120,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_119])).

tff(c_30,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_2'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,B_71)
      | ~ r2_hidden(C_72,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [C_73,A_74] :
      ( ~ r2_hidden(C_73,k1_xboole_0)
      | ~ r2_hidden(C_73,A_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_96,plain,(
    ! [A_74] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0),A_74)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_83])).

tff(c_98,plain,(
    ! [A_75] : ~ r2_hidden('#skF_2'(k1_xboole_0),A_75) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_103])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:18:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.23  
% 1.80/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.93/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.93/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.93/1.23  
% 1.93/1.24  tff(f_80, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.93/1.24  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.93/1.24  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.93/1.24  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.93/1.24  tff(f_71, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.93/1.24  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.93/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.93/1.24  tff(c_38, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.93/1.24  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.93/1.24  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.24  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.93/1.24  tff(c_125, plain, (![A_77]: (k2_xboole_0(k1_relat_1(A_77), k2_relat_1(A_77))=k3_relat_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.24  tff(c_134, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_125])).
% 1.93/1.24  tff(c_140, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8, c_134])).
% 1.93/1.24  tff(c_141, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_140])).
% 1.93/1.24  tff(c_104, plain, (![A_76]: (k2_xboole_0(k1_relat_1(A_76), k2_relat_1(A_76))=k3_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.24  tff(c_113, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_104])).
% 1.93/1.24  tff(c_119, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36, c_113])).
% 1.93/1.24  tff(c_120, plain, (~v1_relat_1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_38, c_119])).
% 1.93/1.24  tff(c_30, plain, (![A_37]: (r2_hidden('#skF_2'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.93/1.24  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.24  tff(c_79, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, B_71) | ~r2_hidden(C_72, A_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.24  tff(c_83, plain, (![C_73, A_74]: (~r2_hidden(C_73, k1_xboole_0) | ~r2_hidden(C_73, A_74))), inference(resolution, [status(thm)], [c_10, c_79])).
% 1.93/1.24  tff(c_96, plain, (![A_74]: (~r2_hidden('#skF_2'(k1_xboole_0), A_74) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_83])).
% 1.93/1.24  tff(c_98, plain, (![A_75]: (~r2_hidden('#skF_2'(k1_xboole_0), A_75))), inference(splitLeft, [status(thm)], [c_96])).
% 1.93/1.24  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_98])).
% 1.93/1.24  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_103])).
% 1.93/1.24  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_96])).
% 1.93/1.24  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_124])).
% 1.93/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  Inference rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Ref     : 0
% 1.93/1.24  #Sup     : 23
% 1.93/1.24  #Fact    : 0
% 1.93/1.24  #Define  : 0
% 1.93/1.24  #Split   : 1
% 1.93/1.24  #Chain   : 0
% 1.93/1.24  #Close   : 0
% 1.93/1.24  
% 1.93/1.24  Ordering : KBO
% 1.93/1.24  
% 1.93/1.24  Simplification rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Subsume      : 2
% 1.93/1.24  #Demod        : 9
% 1.93/1.24  #Tautology    : 15
% 1.93/1.24  #SimpNegUnit  : 6
% 1.93/1.24  #BackRed      : 0
% 1.93/1.24  
% 1.93/1.24  #Partial instantiations: 0
% 1.93/1.24  #Strategies tried      : 1
% 1.93/1.24  
% 1.93/1.24  Timing (in seconds)
% 1.93/1.24  ----------------------
% 1.93/1.24  Preprocessing        : 0.31
% 1.93/1.24  Parsing              : 0.17
% 1.93/1.24  CNF conversion       : 0.02
% 1.93/1.24  Main loop            : 0.12
% 1.93/1.24  Inferencing          : 0.04
% 1.93/1.24  Reduction            : 0.04
% 1.93/1.24  Demodulation         : 0.03
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.02
% 1.93/1.24  Abstraction          : 0.01
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.46
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
