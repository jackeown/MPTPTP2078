%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   55 (  92 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 146 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
        & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_43,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [C_10] :
      ( r1_xboole_0('#skF_2','#skF_3')
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    ! [C_19] : ~ r2_hidden(C_19,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_50,plain,(
    v1_xboole_0(k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_12])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_53])).

tff(c_58,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_16,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_4',k1_xboole_0)
      | ~ r2_hidden(C_10,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_70,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_75,plain,(
    v1_xboole_0(k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_78,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_78])).

tff(c_83,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_91,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_103,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_103])).

tff(c_92,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_93])).

tff(c_96,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_102,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_117,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_102])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:13:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.25  
% 1.71/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.25  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 1.71/1.25  
% 1.71/1.25  %Foreground sorts:
% 1.71/1.25  
% 1.71/1.25  
% 1.71/1.25  %Background operators:
% 1.71/1.25  
% 1.71/1.25  
% 1.71/1.25  %Foreground operators:
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.71/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.71/1.25  
% 1.71/1.26  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.71/1.26  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.71/1.26  tff(f_55, negated_conjecture, ~(![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.71/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.71/1.26  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.71/1.26  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.71/1.26  tff(c_35, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.26  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.26  tff(c_33, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_18])).
% 1.71/1.26  tff(c_43, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_35, c_33])).
% 1.71/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.26  tff(c_14, plain, (![C_10]: (r1_xboole_0('#skF_2', '#skF_3') | ~r2_hidden(C_10, k3_xboole_0('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.26  tff(c_45, plain, (![C_19]: (~r2_hidden(C_19, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_14])).
% 1.71/1.26  tff(c_50, plain, (v1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_45])).
% 1.71/1.26  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.26  tff(c_53, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_12])).
% 1.71/1.26  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_53])).
% 1.71/1.26  tff(c_58, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_14])).
% 1.71/1.26  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.26  tff(c_62, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_6])).
% 1.71/1.26  tff(c_16, plain, (![C_10]: (r2_hidden('#skF_4', k3_xboole_0('#skF_2', '#skF_3')) | ~r2_hidden(C_10, k3_xboole_0('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.26  tff(c_68, plain, (![C_10]: (r2_hidden('#skF_4', k1_xboole_0) | ~r2_hidden(C_10, k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16])).
% 1.71/1.26  tff(c_70, plain, (![C_20]: (~r2_hidden(C_20, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_68])).
% 1.71/1.26  tff(c_75, plain, (v1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_70])).
% 1.71/1.26  tff(c_78, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_12])).
% 1.71/1.26  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_78])).
% 1.71/1.26  tff(c_83, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_68])).
% 1.71/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.26  tff(c_86, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_2])).
% 1.71/1.26  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_86])).
% 1.71/1.26  tff(c_91, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.71/1.26  tff(c_103, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.26  tff(c_111, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_103])).
% 1.71/1.26  tff(c_92, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 1.71/1.26  tff(c_20, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.26  tff(c_93, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_20])).
% 1.71/1.26  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_93])).
% 1.71/1.26  tff(c_96, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 1.71/1.26  tff(c_102, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_2])).
% 1.71/1.26  tff(c_117, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_102])).
% 1.71/1.26  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_117])).
% 1.71/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.26  
% 1.71/1.26  Inference rules
% 1.71/1.26  ----------------------
% 1.71/1.26  #Ref     : 0
% 1.71/1.26  #Sup     : 17
% 1.71/1.26  #Fact    : 0
% 1.71/1.26  #Define  : 0
% 1.71/1.26  #Split   : 4
% 1.71/1.26  #Chain   : 0
% 1.71/1.26  #Close   : 0
% 1.71/1.26  
% 1.71/1.26  Ordering : KBO
% 1.71/1.26  
% 1.71/1.26  Simplification rules
% 1.71/1.26  ----------------------
% 1.71/1.26  #Subsume      : 1
% 1.71/1.26  #Demod        : 9
% 1.71/1.26  #Tautology    : 9
% 1.71/1.26  #SimpNegUnit  : 2
% 1.71/1.26  #BackRed      : 2
% 1.71/1.26  
% 1.71/1.26  #Partial instantiations: 0
% 1.71/1.26  #Strategies tried      : 1
% 1.71/1.26  
% 1.71/1.26  Timing (in seconds)
% 1.71/1.26  ----------------------
% 1.71/1.26  Preprocessing        : 0.26
% 1.71/1.26  Parsing              : 0.15
% 1.71/1.26  CNF conversion       : 0.02
% 1.71/1.26  Main loop            : 0.13
% 1.71/1.26  Inferencing          : 0.05
% 1.71/1.26  Reduction            : 0.03
% 1.71/1.26  Demodulation         : 0.02
% 1.71/1.26  BG Simplification    : 0.01
% 1.71/1.26  Subsumption          : 0.02
% 1.71/1.26  Abstraction          : 0.00
% 1.71/1.27  MUC search           : 0.00
% 1.71/1.27  Cooper               : 0.00
% 1.71/1.27  Total                : 0.41
% 1.71/1.27  Index Insertion      : 0.00
% 1.71/1.27  Index Deletion       : 0.00
% 1.71/1.27  Index Matching       : 0.00
% 1.71/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
