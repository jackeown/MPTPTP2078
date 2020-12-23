%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 131 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 280 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_36,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_ordinal1(B_5,A_4)
      | r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_354,plain,(
    ! [B_75] :
      ( ~ v3_ordinal1(B_75)
      | r1_ordinal1(B_75,B_75) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_30,plain,(
    ! [B_15] : r2_hidden(B_15,k1_ordinal1(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,
    ( r2_hidden('#skF_2',k1_ordinal1('#skF_3'))
    | r1_ordinal1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_67,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ r1_ordinal1(A_11,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ! [A_22] :
      ( v1_ordinal1(A_22)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    v1_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | ~ r2_xboole_0(A_45,B_46)
      | ~ v3_ordinal1(B_46)
      | ~ v1_ordinal1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_184,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v1_ordinal1(A_50)
      | B_51 = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,B_15)
      | r2_hidden(A_14,k1_ordinal1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_40])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_194,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_87])).

tff(c_202,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36,c_194])).

tff(c_206,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_209,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_67,c_209])).

tff(c_214,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_83])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_217])).

tff(c_226,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_65,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_225,plain,(
    r2_hidden('#skF_2',k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_273,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | r2_hidden(A_66,B_65)
      | ~ r2_hidden(A_66,k1_ordinal1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_291,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_273])).

tff(c_292,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_16,plain,(
    ! [B_10,A_7] :
      ( r1_tarski(B_10,A_7)
      | ~ r2_hidden(B_10,A_7)
      | ~ v1_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_295,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_292,c_16])).

tff(c_298,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_295])).

tff(c_299,plain,(
    ! [A_67,B_68] :
      ( r1_ordinal1(A_67,B_68)
      | ~ r1_tarski(A_67,B_68)
      | ~ v3_ordinal1(B_68)
      | ~ v3_ordinal1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_302,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_299])).

tff(c_308,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_302])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_308])).

tff(c_311,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_314,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_226])).

tff(c_357,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_354,c_314])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 2.37/1.33  
% 2.37/1.33  %Foreground sorts:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Background operators:
% 2.37/1.33  
% 2.37/1.33  
% 2.37/1.33  %Foreground operators:
% 2.37/1.33  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.33  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.37/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.33  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.37/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.33  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.37/1.33  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.37/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.33  
% 2.37/1.35  tff(f_90, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.37/1.35  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.37/1.35  tff(f_71, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.37/1.35  tff(f_63, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.37/1.35  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.37/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.37/1.35  tff(f_80, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.37/1.35  tff(f_55, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.37/1.35  tff(c_36, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.37/1.35  tff(c_12, plain, (![B_5, A_4]: (r1_ordinal1(B_5, A_4) | r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.35  tff(c_354, plain, (![B_75]: (~v3_ordinal1(B_75) | r1_ordinal1(B_75, B_75))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 2.37/1.35  tff(c_30, plain, (![B_15]: (r2_hidden(B_15, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.35  tff(c_38, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.37/1.35  tff(c_46, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_3')) | r1_ordinal1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.37/1.35  tff(c_67, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 2.37/1.35  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~r1_ordinal1(A_11, B_12) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.37/1.35  tff(c_58, plain, (![A_22]: (v1_ordinal1(A_22) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.35  tff(c_66, plain, (v1_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.37/1.35  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.35  tff(c_159, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | ~r2_xboole_0(A_45, B_46) | ~v3_ordinal1(B_46) | ~v1_ordinal1(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.37/1.35  tff(c_184, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | ~v3_ordinal1(B_51) | ~v1_ordinal1(A_50) | B_51=A_50 | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_2, c_159])).
% 2.37/1.35  tff(c_32, plain, (![A_14, B_15]: (~r2_hidden(A_14, B_15) | r2_hidden(A_14, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.35  tff(c_40, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.37/1.35  tff(c_83, plain, (~r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_40])).
% 2.37/1.35  tff(c_87, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_83])).
% 2.37/1.35  tff(c_194, plain, (~v3_ordinal1('#skF_3') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_184, c_87])).
% 2.37/1.35  tff(c_202, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36, c_194])).
% 2.37/1.35  tff(c_206, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_202])).
% 2.37/1.35  tff(c_209, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_206])).
% 2.37/1.35  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_67, c_209])).
% 2.37/1.35  tff(c_214, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_202])).
% 2.37/1.35  tff(c_217, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_83])).
% 2.37/1.35  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_217])).
% 2.37/1.35  tff(c_226, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 2.37/1.35  tff(c_65, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.37/1.35  tff(c_225, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 2.37/1.35  tff(c_273, plain, (![B_65, A_66]: (B_65=A_66 | r2_hidden(A_66, B_65) | ~r2_hidden(A_66, k1_ordinal1(B_65)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.35  tff(c_291, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_225, c_273])).
% 2.37/1.35  tff(c_292, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_291])).
% 2.37/1.35  tff(c_16, plain, (![B_10, A_7]: (r1_tarski(B_10, A_7) | ~r2_hidden(B_10, A_7) | ~v1_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.35  tff(c_295, plain, (r1_tarski('#skF_2', '#skF_3') | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_292, c_16])).
% 2.37/1.35  tff(c_298, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_295])).
% 2.37/1.35  tff(c_299, plain, (![A_67, B_68]: (r1_ordinal1(A_67, B_68) | ~r1_tarski(A_67, B_68) | ~v3_ordinal1(B_68) | ~v3_ordinal1(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.37/1.35  tff(c_302, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_298, c_299])).
% 2.37/1.35  tff(c_308, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_302])).
% 2.37/1.35  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_308])).
% 2.37/1.35  tff(c_311, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_291])).
% 2.37/1.35  tff(c_314, plain, (~r1_ordinal1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_226])).
% 2.37/1.35  tff(c_357, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_354, c_314])).
% 2.37/1.35  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_357])).
% 2.37/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  Inference rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Ref     : 0
% 2.37/1.35  #Sup     : 48
% 2.37/1.35  #Fact    : 4
% 2.37/1.35  #Define  : 0
% 2.37/1.35  #Split   : 4
% 2.37/1.35  #Chain   : 0
% 2.37/1.35  #Close   : 0
% 2.37/1.35  
% 2.37/1.35  Ordering : KBO
% 2.37/1.35  
% 2.37/1.35  Simplification rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Subsume      : 3
% 2.37/1.35  #Demod        : 30
% 2.37/1.35  #Tautology    : 26
% 2.37/1.35  #SimpNegUnit  : 1
% 2.37/1.35  #BackRed      : 11
% 2.37/1.35  
% 2.37/1.35  #Partial instantiations: 0
% 2.37/1.35  #Strategies tried      : 1
% 2.37/1.35  
% 2.37/1.35  Timing (in seconds)
% 2.37/1.35  ----------------------
% 2.37/1.35  Preprocessing        : 0.29
% 2.37/1.35  Parsing              : 0.16
% 2.37/1.35  CNF conversion       : 0.02
% 2.37/1.35  Main loop            : 0.29
% 2.37/1.35  Inferencing          : 0.12
% 2.37/1.35  Reduction            : 0.07
% 2.37/1.35  Demodulation         : 0.05
% 2.37/1.35  BG Simplification    : 0.02
% 2.37/1.35  Subsumption          : 0.05
% 2.37/1.35  Abstraction          : 0.01
% 2.37/1.35  MUC search           : 0.00
% 2.37/1.35  Cooper               : 0.00
% 2.37/1.35  Total                : 0.61
% 2.37/1.35  Index Insertion      : 0.00
% 2.37/1.35  Index Deletion       : 0.00
% 2.37/1.36  Index Matching       : 0.00
% 2.37/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
