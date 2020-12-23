%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   45 (  95 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 260 expanded)
%              Number of equality atoms :   26 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_9,B_12] :
      ( k1_funct_1(A_9,B_12) = k1_xboole_0
      | r2_hidden(B_12,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_212,plain,(
    ! [C_58,B_59,A_60] :
      ( k1_funct_1(k7_relat_1(C_58,B_59),A_60) = k1_funct_1(C_58,A_60)
      | ~ r2_hidden(A_60,k3_xboole_0(k1_relat_1(C_58),B_59))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_533,plain,(
    ! [C_87,B_88,D_89] :
      ( k1_funct_1(k7_relat_1(C_87,B_88),D_89) = k1_funct_1(C_87,D_89)
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ r2_hidden(D_89,B_88)
      | ~ r2_hidden(D_89,k1_relat_1(C_87)) ) ),
    inference(resolution,[status(thm)],[c_2,c_212])).

tff(c_622,plain,(
    ! [A_93,B_94,B_95] :
      ( k1_funct_1(k7_relat_1(A_93,B_94),B_95) = k1_funct_1(A_93,B_95)
      | ~ r2_hidden(B_95,B_94)
      | k1_funct_1(A_93,B_95) = k1_xboole_0
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_28,c_533])).

tff(c_38,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_635,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_38])).

tff(c_646,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_635])).

tff(c_649,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_38])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( v1_funct_1(k7_relat_1(A_14,B_15))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_171,plain,(
    ! [C_55,B_56,A_57] :
      ( k1_funct_1(k7_relat_1(C_55,B_56),A_57) = k1_funct_1(C_55,A_57)
      | ~ r2_hidden(A_57,k1_relat_1(k7_relat_1(C_55,B_56)))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2243,plain,(
    ! [C_205,B_206,B_207] :
      ( k1_funct_1(k7_relat_1(C_205,B_206),B_207) = k1_funct_1(C_205,B_207)
      | ~ v1_funct_1(C_205)
      | ~ v1_relat_1(C_205)
      | k1_funct_1(k7_relat_1(C_205,B_206),B_207) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(C_205,B_206))
      | ~ v1_relat_1(k7_relat_1(C_205,B_206)) ) ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_2444,plain,(
    ! [A_211,B_212,B_213] :
      ( k1_funct_1(k7_relat_1(A_211,B_212),B_213) = k1_funct_1(A_211,B_213)
      | ~ v1_funct_1(A_211)
      | k1_funct_1(k7_relat_1(A_211,B_212),B_213) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_211,B_212))
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_20,c_2243])).

tff(c_2452,plain,(
    ! [A_214,B_215,B_216] :
      ( k1_funct_1(k7_relat_1(A_214,B_215),B_216) = k1_funct_1(A_214,B_216)
      | k1_funct_1(k7_relat_1(A_214,B_215),B_216) = k1_xboole_0
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(resolution,[status(thm)],[c_30,c_2444])).

tff(c_2458,plain,
    ( k1_funct_1('#skF_5','#skF_3') != k1_xboole_0
    | k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2452,c_649])).

tff(c_2480,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_646,c_2458])).

tff(c_2482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_2480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.89  
% 4.90/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.89  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.90/1.89  
% 4.90/1.89  %Foreground sorts:
% 4.90/1.89  
% 4.90/1.89  
% 4.90/1.89  %Background operators:
% 4.90/1.89  
% 4.90/1.89  
% 4.90/1.89  %Foreground operators:
% 4.90/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.90/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.90/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.90/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.90/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.90/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.90/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.90/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.90/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.90/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.90/1.89  
% 4.90/1.90  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 4.90/1.90  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.90/1.90  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.90/1.90  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 4.90/1.90  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.90/1.90  tff(f_38, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.90/1.90  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 4.90/1.90  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.90/1.90  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.90/1.90  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.90/1.90  tff(c_28, plain, (![A_9, B_12]: (k1_funct_1(A_9, B_12)=k1_xboole_0 | r2_hidden(B_12, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.90/1.90  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.90/1.90  tff(c_212, plain, (![C_58, B_59, A_60]: (k1_funct_1(k7_relat_1(C_58, B_59), A_60)=k1_funct_1(C_58, A_60) | ~r2_hidden(A_60, k3_xboole_0(k1_relat_1(C_58), B_59)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.90/1.90  tff(c_533, plain, (![C_87, B_88, D_89]: (k1_funct_1(k7_relat_1(C_87, B_88), D_89)=k1_funct_1(C_87, D_89) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87) | ~r2_hidden(D_89, B_88) | ~r2_hidden(D_89, k1_relat_1(C_87)))), inference(resolution, [status(thm)], [c_2, c_212])).
% 4.90/1.90  tff(c_622, plain, (![A_93, B_94, B_95]: (k1_funct_1(k7_relat_1(A_93, B_94), B_95)=k1_funct_1(A_93, B_95) | ~r2_hidden(B_95, B_94) | k1_funct_1(A_93, B_95)=k1_xboole_0 | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_28, c_533])).
% 4.90/1.90  tff(c_38, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.90/1.90  tff(c_635, plain, (~r2_hidden('#skF_3', '#skF_4') | k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_622, c_38])).
% 4.90/1.90  tff(c_646, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_635])).
% 4.90/1.90  tff(c_649, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_646, c_38])).
% 4.90/1.90  tff(c_30, plain, (![A_14, B_15]: (v1_funct_1(k7_relat_1(A_14, B_15)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.90/1.90  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.90/1.90  tff(c_171, plain, (![C_55, B_56, A_57]: (k1_funct_1(k7_relat_1(C_55, B_56), A_57)=k1_funct_1(C_55, A_57) | ~r2_hidden(A_57, k1_relat_1(k7_relat_1(C_55, B_56))) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.90/1.90  tff(c_2243, plain, (![C_205, B_206, B_207]: (k1_funct_1(k7_relat_1(C_205, B_206), B_207)=k1_funct_1(C_205, B_207) | ~v1_funct_1(C_205) | ~v1_relat_1(C_205) | k1_funct_1(k7_relat_1(C_205, B_206), B_207)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(C_205, B_206)) | ~v1_relat_1(k7_relat_1(C_205, B_206)))), inference(resolution, [status(thm)], [c_28, c_171])).
% 4.90/1.90  tff(c_2444, plain, (![A_211, B_212, B_213]: (k1_funct_1(k7_relat_1(A_211, B_212), B_213)=k1_funct_1(A_211, B_213) | ~v1_funct_1(A_211) | k1_funct_1(k7_relat_1(A_211, B_212), B_213)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(A_211, B_212)) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_20, c_2243])).
% 4.90/1.90  tff(c_2452, plain, (![A_214, B_215, B_216]: (k1_funct_1(k7_relat_1(A_214, B_215), B_216)=k1_funct_1(A_214, B_216) | k1_funct_1(k7_relat_1(A_214, B_215), B_216)=k1_xboole_0 | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(resolution, [status(thm)], [c_30, c_2444])).
% 4.90/1.90  tff(c_2458, plain, (k1_funct_1('#skF_5', '#skF_3')!=k1_xboole_0 | k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2452, c_649])).
% 4.90/1.90  tff(c_2480, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_646, c_2458])).
% 4.90/1.90  tff(c_2482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_2480])).
% 4.90/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.90  
% 4.90/1.90  Inference rules
% 4.90/1.90  ----------------------
% 4.90/1.90  #Ref     : 0
% 4.90/1.90  #Sup     : 508
% 4.90/1.90  #Fact    : 1
% 4.90/1.90  #Define  : 0
% 4.90/1.90  #Split   : 1
% 4.90/1.90  #Chain   : 0
% 4.90/1.90  #Close   : 0
% 4.90/1.90  
% 4.90/1.90  Ordering : KBO
% 4.90/1.90  
% 4.90/1.90  Simplification rules
% 4.90/1.90  ----------------------
% 4.90/1.90  #Subsume      : 116
% 4.90/1.90  #Demod        : 199
% 4.90/1.90  #Tautology    : 47
% 4.90/1.90  #SimpNegUnit  : 1
% 4.90/1.90  #BackRed      : 1
% 4.90/1.90  
% 4.90/1.90  #Partial instantiations: 0
% 4.90/1.90  #Strategies tried      : 1
% 4.90/1.90  
% 4.90/1.90  Timing (in seconds)
% 4.90/1.90  ----------------------
% 4.90/1.90  Preprocessing        : 0.31
% 4.90/1.90  Parsing              : 0.17
% 4.90/1.90  CNF conversion       : 0.02
% 4.90/1.90  Main loop            : 0.83
% 4.90/1.90  Inferencing          : 0.32
% 4.90/1.90  Reduction            : 0.20
% 4.90/1.90  Demodulation         : 0.14
% 4.90/1.90  BG Simplification    : 0.05
% 4.90/1.90  Subsumption          : 0.19
% 4.90/1.90  Abstraction          : 0.08
% 4.90/1.90  MUC search           : 0.00
% 4.90/1.90  Cooper               : 0.00
% 4.90/1.90  Total                : 1.16
% 4.90/1.90  Index Insertion      : 0.00
% 4.90/1.90  Index Deletion       : 0.00
% 4.90/1.90  Index Matching       : 0.00
% 4.90/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
