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
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 146 expanded)
%              Number of equality atoms :   12 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [C_24,A_9] :
      ( r2_hidden(k4_tarski(C_24,'#skF_6'(A_9,k1_relat_1(A_9),C_24)),A_9)
      | ~ r2_hidden(C_24,k1_relat_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_279,plain,(
    ! [C_93,A_94] :
      ( r2_hidden(k4_tarski(C_93,'#skF_6'(A_94,k1_relat_1(A_94),C_93)),A_94)
      | ~ r2_hidden(C_93,k1_relat_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_142,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,B_67)
      | ~ r2_hidden(C_68,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [C_68,A_8] :
      ( ~ r2_hidden(C_68,k1_xboole_0)
      | ~ r2_hidden(C_68,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_398,plain,(
    ! [C_109,A_110] :
      ( ~ r2_hidden(k4_tarski(C_109,'#skF_6'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_109)),A_110)
      | ~ r2_hidden(C_109,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_279,c_145])).

tff(c_451,plain,(
    ! [C_113] : ~ r2_hidden(C_113,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_398])).

tff(c_501,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_451])).

tff(c_424,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_398])).

tff(c_502,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_424])).

tff(c_30,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_39,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_36])).

tff(c_28,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ r2_hidden(B_52,k11_relat_1(C_53,A_51))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k1_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(C_24,D_27),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(A_54,k1_relat_1(C_55))
      | ~ r2_hidden(B_56,k11_relat_1(C_55,A_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_81,c_14])).

tff(c_111,plain,(
    ! [A_57,C_58] :
      ( r2_hidden(A_57,k1_relat_1(C_58))
      | ~ v1_relat_1(C_58)
      | k11_relat_1(C_58,A_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_122,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_39])).

tff(c_127,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_122])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_127])).

tff(c_130,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_137,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_36])).

tff(c_26,plain,(
    ! [B_29,C_30,A_28] :
      ( r2_hidden(B_29,k11_relat_1(C_30,A_28))
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_914,plain,(
    ! [A_139,C_140] :
      ( r2_hidden('#skF_6'(A_139,k1_relat_1(A_139),C_140),k11_relat_1(A_139,C_140))
      | ~ v1_relat_1(A_139)
      | ~ r2_hidden(C_140,k1_relat_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_279,c_26])).

tff(c_928,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_914])).

tff(c_933,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_28,c_928])).

tff(c_935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_502,c_933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.49  
% 3.33/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.49  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 3.33/1.49  
% 3.33/1.49  %Foreground sorts:
% 3.33/1.49  
% 3.33/1.49  
% 3.33/1.49  %Background operators:
% 3.33/1.49  
% 3.33/1.49  
% 3.33/1.49  %Foreground operators:
% 3.33/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.33/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.33/1.49  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.33/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.33/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.33/1.49  
% 3.33/1.51  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.33/1.51  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.33/1.51  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.33/1.51  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.33/1.51  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.33/1.51  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.33/1.51  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.51  tff(c_12, plain, (![C_24, A_9]: (r2_hidden(k4_tarski(C_24, '#skF_6'(A_9, k1_relat_1(A_9), C_24)), A_9) | ~r2_hidden(C_24, k1_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.51  tff(c_279, plain, (![C_93, A_94]: (r2_hidden(k4_tarski(C_93, '#skF_6'(A_94, k1_relat_1(A_94), C_93)), A_94) | ~r2_hidden(C_93, k1_relat_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.51  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.33/1.51  tff(c_142, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, B_67) | ~r2_hidden(C_68, A_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.51  tff(c_145, plain, (![C_68, A_8]: (~r2_hidden(C_68, k1_xboole_0) | ~r2_hidden(C_68, A_8))), inference(resolution, [status(thm)], [c_10, c_142])).
% 3.33/1.51  tff(c_398, plain, (![C_109, A_110]: (~r2_hidden(k4_tarski(C_109, '#skF_6'(k1_xboole_0, k1_relat_1(k1_xboole_0), C_109)), A_110) | ~r2_hidden(C_109, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_279, c_145])).
% 3.33/1.51  tff(c_451, plain, (![C_113]: (~r2_hidden(C_113, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_398])).
% 3.33/1.51  tff(c_501, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_451])).
% 3.33/1.51  tff(c_424, plain, (![C_24]: (~r2_hidden(C_24, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_398])).
% 3.33/1.51  tff(c_502, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_424])).
% 3.33/1.51  tff(c_30, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.51  tff(c_39, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.33/1.51  tff(c_36, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.51  tff(c_42, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_39, c_36])).
% 3.33/1.51  tff(c_28, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.51  tff(c_81, plain, (![A_51, B_52, C_53]: (r2_hidden(k4_tarski(A_51, B_52), C_53) | ~r2_hidden(B_52, k11_relat_1(C_53, A_51)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.51  tff(c_14, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k1_relat_1(A_9)) | ~r2_hidden(k4_tarski(C_24, D_27), A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.51  tff(c_94, plain, (![A_54, C_55, B_56]: (r2_hidden(A_54, k1_relat_1(C_55)) | ~r2_hidden(B_56, k11_relat_1(C_55, A_54)) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_81, c_14])).
% 3.33/1.51  tff(c_111, plain, (![A_57, C_58]: (r2_hidden(A_57, k1_relat_1(C_58)) | ~v1_relat_1(C_58) | k11_relat_1(C_58, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_94])).
% 3.33/1.51  tff(c_122, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_39])).
% 3.33/1.51  tff(c_127, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_122])).
% 3.33/1.51  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_127])).
% 3.33/1.51  tff(c_130, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 3.33/1.51  tff(c_137, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_36])).
% 3.33/1.51  tff(c_26, plain, (![B_29, C_30, A_28]: (r2_hidden(B_29, k11_relat_1(C_30, A_28)) | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.51  tff(c_914, plain, (![A_139, C_140]: (r2_hidden('#skF_6'(A_139, k1_relat_1(A_139), C_140), k11_relat_1(A_139, C_140)) | ~v1_relat_1(A_139) | ~r2_hidden(C_140, k1_relat_1(A_139)))), inference(resolution, [status(thm)], [c_279, c_26])).
% 3.33/1.51  tff(c_928, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_914])).
% 3.33/1.51  tff(c_933, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_28, c_928])).
% 3.33/1.51  tff(c_935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_502, c_933])).
% 3.33/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.51  
% 3.33/1.51  Inference rules
% 3.33/1.51  ----------------------
% 3.33/1.51  #Ref     : 0
% 3.33/1.51  #Sup     : 188
% 3.33/1.51  #Fact    : 0
% 3.33/1.51  #Define  : 0
% 3.33/1.51  #Split   : 2
% 3.33/1.51  #Chain   : 0
% 3.33/1.51  #Close   : 0
% 3.33/1.51  
% 3.33/1.51  Ordering : KBO
% 3.33/1.51  
% 3.33/1.51  Simplification rules
% 3.33/1.51  ----------------------
% 3.33/1.51  #Subsume      : 40
% 3.33/1.51  #Demod        : 86
% 3.33/1.51  #Tautology    : 49
% 3.33/1.51  #SimpNegUnit  : 17
% 3.33/1.51  #BackRed      : 1
% 3.33/1.51  
% 3.33/1.51  #Partial instantiations: 0
% 3.33/1.51  #Strategies tried      : 1
% 3.33/1.51  
% 3.33/1.51  Timing (in seconds)
% 3.33/1.51  ----------------------
% 3.33/1.51  Preprocessing        : 0.30
% 3.33/1.51  Parsing              : 0.16
% 3.33/1.51  CNF conversion       : 0.02
% 3.33/1.51  Main loop            : 0.44
% 3.33/1.51  Inferencing          : 0.17
% 3.33/1.51  Reduction            : 0.11
% 3.33/1.51  Demodulation         : 0.07
% 3.33/1.51  BG Simplification    : 0.03
% 3.33/1.51  Subsumption          : 0.10
% 3.33/1.51  Abstraction          : 0.02
% 3.33/1.51  MUC search           : 0.00
% 3.33/1.51  Cooper               : 0.00
% 3.33/1.51  Total                : 0.77
% 3.33/1.51  Index Insertion      : 0.00
% 3.33/1.51  Index Deletion       : 0.00
% 3.33/1.51  Index Matching       : 0.00
% 3.33/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
