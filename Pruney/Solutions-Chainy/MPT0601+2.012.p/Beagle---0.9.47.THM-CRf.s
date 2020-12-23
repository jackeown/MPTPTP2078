%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 138 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_43,plain,(
    k11_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34])).

tff(c_44,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_1'(A_19,B_20),B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    ! [A_19,A_6] :
      ( '#skF_1'(A_19,k1_tarski(A_6)) = A_6
      | r1_xboole_0(A_19,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_74,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(B_32,A_33) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_32),A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_215,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,k1_tarski(A_60)) = k1_xboole_0
      | ~ v1_relat_1(B_59)
      | '#skF_1'(k1_relat_1(B_59),k1_tarski(A_60)) = A_60 ) ),
    inference(resolution,[status(thm)],[c_49,c_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1724,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(A_151,k1_relat_1(B_152))
      | r1_xboole_0(k1_relat_1(B_152),k1_tarski(A_151))
      | k9_relat_1(B_152,k1_tarski(A_151)) = k1_xboole_0
      | ~ v1_relat_1(B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_6])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,A_14) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1732,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(A_153,k1_relat_1(B_154))
      | k9_relat_1(B_154,k1_tarski(A_153)) = k1_xboole_0
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_1724,c_22])).

tff(c_1775,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1732,c_42])).

tff(c_1789,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1775])).

tff(c_20,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1793,plain,
    ( k11_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_20])).

tff(c_1800,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1793])).

tff(c_1802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_1800])).

tff(c_1803,plain,(
    k11_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1804,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1847,plain,(
    ! [B_170,A_171] :
      ( r1_xboole_0(k1_relat_1(B_170),A_171)
      | k9_relat_1(B_170,A_171) != k1_xboole_0
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1963,plain,(
    ! [C_191,A_192,B_193] :
      ( ~ r2_hidden(C_191,A_192)
      | ~ r2_hidden(C_191,k1_relat_1(B_193))
      | k9_relat_1(B_193,A_192) != k1_xboole_0
      | ~ v1_relat_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_1847,c_2])).

tff(c_1989,plain,(
    ! [C_195,B_196] :
      ( ~ r2_hidden(C_195,k1_relat_1(B_196))
      | k9_relat_1(B_196,k1_tarski(C_195)) != k1_xboole_0
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_10,c_1963])).

tff(c_2008,plain,
    ( k9_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1804,c_1989])).

tff(c_2015,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2008])).

tff(c_2041,plain,
    ( k11_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2015])).

tff(c_2044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1803,c_2041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.59  
% 3.47/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.59  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.47/1.59  
% 3.47/1.59  %Foreground sorts:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Background operators:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Foreground operators:
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.47/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.47/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.59  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.59  
% 3.47/1.61  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.47/1.61  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.47/1.61  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.47/1.61  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.47/1.61  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.47/1.61  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.47/1.61  tff(c_28, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.47/1.61  tff(c_42, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_28])).
% 3.47/1.61  tff(c_34, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5')) | k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.47/1.61  tff(c_43, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_34])).
% 3.47/1.61  tff(c_44, plain, (![A_19, B_20]: (r2_hidden('#skF_1'(A_19, B_20), B_20) | r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.61  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.61  tff(c_49, plain, (![A_19, A_6]: ('#skF_1'(A_19, k1_tarski(A_6))=A_6 | r1_xboole_0(A_19, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_44, c_8])).
% 3.47/1.61  tff(c_74, plain, (![B_32, A_33]: (k9_relat_1(B_32, A_33)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_32), A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.61  tff(c_215, plain, (![B_59, A_60]: (k9_relat_1(B_59, k1_tarski(A_60))=k1_xboole_0 | ~v1_relat_1(B_59) | '#skF_1'(k1_relat_1(B_59), k1_tarski(A_60))=A_60)), inference(resolution, [status(thm)], [c_49, c_74])).
% 3.47/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.61  tff(c_1724, plain, (![A_151, B_152]: (r2_hidden(A_151, k1_relat_1(B_152)) | r1_xboole_0(k1_relat_1(B_152), k1_tarski(A_151)) | k9_relat_1(B_152, k1_tarski(A_151))=k1_xboole_0 | ~v1_relat_1(B_152))), inference(superposition, [status(thm), theory('equality')], [c_215, c_6])).
% 3.47/1.61  tff(c_22, plain, (![B_15, A_14]: (k9_relat_1(B_15, A_14)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.61  tff(c_1732, plain, (![A_153, B_154]: (r2_hidden(A_153, k1_relat_1(B_154)) | k9_relat_1(B_154, k1_tarski(A_153))=k1_xboole_0 | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_1724, c_22])).
% 3.47/1.61  tff(c_1775, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1732, c_42])).
% 3.47/1.61  tff(c_1789, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1775])).
% 3.47/1.61  tff(c_20, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.61  tff(c_1793, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1789, c_20])).
% 3.47/1.61  tff(c_1800, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1793])).
% 3.47/1.61  tff(c_1802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_1800])).
% 3.47/1.61  tff(c_1803, plain, (k11_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.47/1.61  tff(c_1804, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 3.47/1.61  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.61  tff(c_1847, plain, (![B_170, A_171]: (r1_xboole_0(k1_relat_1(B_170), A_171) | k9_relat_1(B_170, A_171)!=k1_xboole_0 | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.61  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.61  tff(c_1963, plain, (![C_191, A_192, B_193]: (~r2_hidden(C_191, A_192) | ~r2_hidden(C_191, k1_relat_1(B_193)) | k9_relat_1(B_193, A_192)!=k1_xboole_0 | ~v1_relat_1(B_193))), inference(resolution, [status(thm)], [c_1847, c_2])).
% 3.47/1.61  tff(c_1989, plain, (![C_195, B_196]: (~r2_hidden(C_195, k1_relat_1(B_196)) | k9_relat_1(B_196, k1_tarski(C_195))!=k1_xboole_0 | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_10, c_1963])).
% 3.47/1.61  tff(c_2008, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1804, c_1989])).
% 3.47/1.61  tff(c_2015, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2008])).
% 3.47/1.61  tff(c_2041, plain, (k11_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2015])).
% 3.47/1.61  tff(c_2044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1803, c_2041])).
% 3.47/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  Inference rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Ref     : 0
% 3.47/1.61  #Sup     : 491
% 3.47/1.61  #Fact    : 0
% 3.47/1.61  #Define  : 0
% 3.47/1.61  #Split   : 1
% 3.47/1.61  #Chain   : 0
% 3.47/1.61  #Close   : 0
% 3.47/1.61  
% 3.47/1.61  Ordering : KBO
% 3.47/1.61  
% 3.47/1.61  Simplification rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Subsume      : 146
% 3.47/1.61  #Demod        : 105
% 3.47/1.61  #Tautology    : 193
% 3.47/1.61  #SimpNegUnit  : 2
% 3.47/1.61  #BackRed      : 0
% 3.47/1.61  
% 3.47/1.61  #Partial instantiations: 0
% 3.47/1.61  #Strategies tried      : 1
% 3.47/1.61  
% 3.47/1.61  Timing (in seconds)
% 3.47/1.61  ----------------------
% 3.47/1.61  Preprocessing        : 0.28
% 3.47/1.61  Parsing              : 0.15
% 3.47/1.61  CNF conversion       : 0.02
% 3.47/1.61  Main loop            : 0.57
% 3.47/1.61  Inferencing          : 0.22
% 3.47/1.61  Reduction            : 0.13
% 3.47/1.61  Demodulation         : 0.08
% 3.47/1.61  BG Simplification    : 0.03
% 3.47/1.61  Subsumption          : 0.15
% 3.47/1.61  Abstraction          : 0.03
% 3.47/1.61  MUC search           : 0.00
% 3.47/1.61  Cooper               : 0.00
% 3.47/1.61  Total                : 0.87
% 3.47/1.61  Index Insertion      : 0.00
% 3.47/1.61  Index Deletion       : 0.00
% 3.47/1.61  Index Matching       : 0.00
% 3.47/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
