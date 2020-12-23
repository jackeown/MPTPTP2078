%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 113 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_11,C_43] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_66,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_63])).

tff(c_40,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden(k4_tarski(A_56,B_57),C_58)
      | ~ r2_hidden(B_57,k11_relat_1(C_58,A_56))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_172,plain,(
    ! [A_69,C_70,B_71] :
      ( r2_hidden(A_69,k1_relat_1(C_70))
      | ~ r2_hidden(B_71,k11_relat_1(C_70,A_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_121,c_18])).

tff(c_1873,plain,(
    ! [A_136,C_137] :
      ( r2_hidden(A_136,k1_relat_1(C_137))
      | ~ v1_relat_1(C_137)
      | v1_xboole_0(k11_relat_1(C_137,A_136)) ) ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_34,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_34])).

tff(c_1921,plain,
    ( ~ v1_relat_1('#skF_8')
    | v1_xboole_0(k11_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1873,c_95])).

tff(c_1963,plain,(
    v1_xboole_0(k11_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1921])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1988,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1963,c_6])).

tff(c_1998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1988])).

tff(c_1999,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2001,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2001])).

tff(c_2012,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2106,plain,(
    ! [C_158,A_159] :
      ( r2_hidden(k4_tarski(C_158,'#skF_6'(A_159,k1_relat_1(A_159),C_158)),A_159)
      | ~ r2_hidden(C_158,k1_relat_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [B_33,C_34,A_32] :
      ( r2_hidden(B_33,k11_relat_1(C_34,A_32))
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5890,plain,(
    ! [A_280,C_281] :
      ( r2_hidden('#skF_6'(A_280,k1_relat_1(A_280),C_281),k11_relat_1(A_280,C_281))
      | ~ v1_relat_1(A_280)
      | ~ r2_hidden(C_281,k1_relat_1(A_280)) ) ),
    inference(resolution,[status(thm)],[c_2106,c_30])).

tff(c_5945,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2012,c_5890])).

tff(c_5953,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_32,c_5945])).

tff(c_5955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.11  
% 5.78/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.11  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 5.78/2.11  
% 5.78/2.11  %Foreground sorts:
% 5.78/2.11  
% 5.78/2.11  
% 5.78/2.11  %Background operators:
% 5.78/2.11  
% 5.78/2.11  
% 5.78/2.11  %Foreground operators:
% 5.78/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.78/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.78/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.78/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.11  tff('#skF_7', type, '#skF_7': $i).
% 5.78/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.78/2.11  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.78/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.78/2.11  tff('#skF_8', type, '#skF_8': $i).
% 5.78/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.78/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.78/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.78/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.78/2.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.78/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.78/2.11  
% 5.78/2.12  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.78/2.12  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.78/2.12  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.78/2.12  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 5.78/2.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.78/2.12  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 5.78/2.13  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.78/2.13  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.78/2.13  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.78/2.13  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.78/2.13  tff(c_56, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.78/2.13  tff(c_63, plain, (![A_11, C_43]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56])).
% 5.78/2.13  tff(c_66, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_63])).
% 5.78/2.13  tff(c_40, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.78/2.13  tff(c_78, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 5.78/2.13  tff(c_32, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.78/2.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.13  tff(c_121, plain, (![A_56, B_57, C_58]: (r2_hidden(k4_tarski(A_56, B_57), C_58) | ~r2_hidden(B_57, k11_relat_1(C_58, A_56)) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.78/2.13  tff(c_18, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.78/2.13  tff(c_172, plain, (![A_69, C_70, B_71]: (r2_hidden(A_69, k1_relat_1(C_70)) | ~r2_hidden(B_71, k11_relat_1(C_70, A_69)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_121, c_18])).
% 5.78/2.13  tff(c_1873, plain, (![A_136, C_137]: (r2_hidden(A_136, k1_relat_1(C_137)) | ~v1_relat_1(C_137) | v1_xboole_0(k11_relat_1(C_137, A_136)))), inference(resolution, [status(thm)], [c_4, c_172])).
% 5.78/2.13  tff(c_34, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.78/2.13  tff(c_95, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_34])).
% 5.78/2.13  tff(c_1921, plain, (~v1_relat_1('#skF_8') | v1_xboole_0(k11_relat_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_1873, c_95])).
% 5.78/2.13  tff(c_1963, plain, (v1_xboole_0(k11_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1921])).
% 5.78/2.13  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.78/2.13  tff(c_1988, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1963, c_6])).
% 5.78/2.13  tff(c_1998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1988])).
% 5.78/2.13  tff(c_1999, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_40])).
% 5.78/2.13  tff(c_2001, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_34])).
% 5.78/2.13  tff(c_2011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2001])).
% 5.78/2.13  tff(c_2012, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 5.78/2.13  tff(c_2106, plain, (![C_158, A_159]: (r2_hidden(k4_tarski(C_158, '#skF_6'(A_159, k1_relat_1(A_159), C_158)), A_159) | ~r2_hidden(C_158, k1_relat_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.78/2.13  tff(c_30, plain, (![B_33, C_34, A_32]: (r2_hidden(B_33, k11_relat_1(C_34, A_32)) | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.78/2.13  tff(c_5890, plain, (![A_280, C_281]: (r2_hidden('#skF_6'(A_280, k1_relat_1(A_280), C_281), k11_relat_1(A_280, C_281)) | ~v1_relat_1(A_280) | ~r2_hidden(C_281, k1_relat_1(A_280)))), inference(resolution, [status(thm)], [c_2106, c_30])).
% 5.78/2.13  tff(c_5945, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2012, c_5890])).
% 5.78/2.13  tff(c_5953, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_32, c_5945])).
% 5.78/2.13  tff(c_5955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_5953])).
% 5.78/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.13  
% 5.78/2.13  Inference rules
% 5.78/2.13  ----------------------
% 5.78/2.13  #Ref     : 0
% 5.78/2.13  #Sup     : 1491
% 5.78/2.13  #Fact    : 0
% 5.78/2.13  #Define  : 0
% 5.78/2.13  #Split   : 4
% 5.78/2.13  #Chain   : 0
% 5.78/2.13  #Close   : 0
% 5.78/2.13  
% 5.78/2.13  Ordering : KBO
% 5.78/2.13  
% 5.78/2.13  Simplification rules
% 5.78/2.13  ----------------------
% 5.78/2.13  #Subsume      : 463
% 5.78/2.13  #Demod        : 1178
% 5.78/2.13  #Tautology    : 450
% 5.78/2.13  #SimpNegUnit  : 43
% 5.78/2.13  #BackRed      : 4
% 5.78/2.13  
% 5.78/2.13  #Partial instantiations: 0
% 5.78/2.13  #Strategies tried      : 1
% 5.78/2.13  
% 5.78/2.13  Timing (in seconds)
% 5.78/2.13  ----------------------
% 5.88/2.13  Preprocessing        : 0.29
% 5.88/2.13  Parsing              : 0.16
% 5.88/2.13  CNF conversion       : 0.02
% 5.88/2.13  Main loop            : 1.05
% 5.88/2.13  Inferencing          : 0.33
% 5.88/2.13  Reduction            : 0.29
% 5.88/2.13  Demodulation         : 0.20
% 5.88/2.13  BG Simplification    : 0.04
% 5.88/2.13  Subsumption          : 0.32
% 5.88/2.13  Abstraction          : 0.06
% 5.88/2.13  MUC search           : 0.00
% 5.88/2.13  Cooper               : 0.00
% 5.88/2.13  Total                : 1.37
% 5.88/2.13  Index Insertion      : 0.00
% 5.88/2.13  Index Deletion       : 0.00
% 5.88/2.13  Index Matching       : 0.00
% 5.88/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
