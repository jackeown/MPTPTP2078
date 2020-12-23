%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 205 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_63,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_28,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_516,plain,(
    ! [A_79,B_80] :
      ( r1_ordinal1(A_79,B_80)
      | ~ r1_tarski(A_79,B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_521,plain,(
    ! [B_81] :
      ( r1_ordinal1(B_81,B_81)
      | ~ v3_ordinal1(B_81) ) ),
    inference(resolution,[status(thm)],[c_8,c_516])).

tff(c_20,plain,(
    ! [B_10] : r2_hidden(B_10,k1_ordinal1(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_36])).

tff(c_148,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | r1_ordinal1(A_39,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden(A_9,B_10)
      | r2_hidden(A_9,k1_ordinal1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_182,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_74])).

tff(c_206,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_182])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ r1_ordinal1(A_44,B_45)
      | ~ v3_ordinal1(B_45)
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_282,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_ordinal1(A_55,B_54)
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_221,c_4])).

tff(c_320,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_ordinal1(B_61,A_62)
      | ~ r1_ordinal1(A_62,B_61)
      | ~ v3_ordinal1(B_61)
      | ~ v3_ordinal1(A_62) ) ),
    inference(resolution,[status(thm)],[c_14,c_282])).

tff(c_334,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_320])).

tff(c_346,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_81,c_334])).

tff(c_354,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_70])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_354])).

tff(c_359,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_24,plain,(
    ! [B_13,A_11] :
      ( r2_hidden(B_13,A_11)
      | r1_ordinal1(A_11,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_360,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_411,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | r2_hidden(A_73,B_72)
      | ~ r2_hidden(A_73,k1_ordinal1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_421,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_360,c_411])).

tff(c_425,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_425,c_2])).

tff(c_480,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_428])).

tff(c_483,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_480])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_483])).

tff(c_486,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_490,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_359])).

tff(c_524,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_521,c_490])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:45:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.31  
% 2.51/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.31  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.51/1.31  
% 2.51/1.31  %Foreground sorts:
% 2.51/1.31  
% 2.51/1.31  
% 2.51/1.31  %Background operators:
% 2.51/1.31  
% 2.51/1.31  
% 2.51/1.31  %Foreground operators:
% 2.51/1.31  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.51/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.31  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.51/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.31  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.51/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.31  
% 2.51/1.33  tff(f_73, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.51/1.33  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.33  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.51/1.33  tff(f_54, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.51/1.33  tff(f_63, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.51/1.33  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.51/1.33  tff(c_28, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.51/1.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.51/1.33  tff(c_516, plain, (![A_79, B_80]: (r1_ordinal1(A_79, B_80) | ~r1_tarski(A_79, B_80) | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_79))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.33  tff(c_521, plain, (![B_81]: (r1_ordinal1(B_81, B_81) | ~v3_ordinal1(B_81))), inference(resolution, [status(thm)], [c_8, c_516])).
% 2.51/1.33  tff(c_20, plain, (![B_10]: (r2_hidden(B_10, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.33  tff(c_26, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.51/1.33  tff(c_30, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.51/1.33  tff(c_70, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.51/1.33  tff(c_36, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.51/1.33  tff(c_81, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_36])).
% 2.51/1.33  tff(c_148, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | r1_ordinal1(A_39, B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.33  tff(c_22, plain, (![A_9, B_10]: (~r2_hidden(A_9, B_10) | r2_hidden(A_9, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.33  tff(c_74, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_70])).
% 2.51/1.33  tff(c_182, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_148, c_74])).
% 2.51/1.33  tff(c_206, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_182])).
% 2.51/1.33  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.33  tff(c_221, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~r1_ordinal1(A_44, B_45) | ~v3_ordinal1(B_45) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.33  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.51/1.33  tff(c_282, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_ordinal1(A_55, B_54) | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_221, c_4])).
% 2.51/1.33  tff(c_320, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_ordinal1(B_61, A_62) | ~r1_ordinal1(A_62, B_61) | ~v3_ordinal1(B_61) | ~v3_ordinal1(A_62))), inference(resolution, [status(thm)], [c_14, c_282])).
% 2.51/1.33  tff(c_334, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_206, c_320])).
% 2.51/1.33  tff(c_346, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_81, c_334])).
% 2.51/1.33  tff(c_354, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_70])).
% 2.51/1.33  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_354])).
% 2.51/1.33  tff(c_359, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.51/1.33  tff(c_24, plain, (![B_13, A_11]: (r2_hidden(B_13, A_11) | r1_ordinal1(A_11, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.33  tff(c_360, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 2.51/1.33  tff(c_411, plain, (![B_72, A_73]: (B_72=A_73 | r2_hidden(A_73, B_72) | ~r2_hidden(A_73, k1_ordinal1(B_72)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.33  tff(c_421, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_360, c_411])).
% 2.51/1.33  tff(c_425, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_421])).
% 2.51/1.33  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.51/1.33  tff(c_428, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_425, c_2])).
% 2.51/1.33  tff(c_480, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_428])).
% 2.51/1.33  tff(c_483, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_480])).
% 2.51/1.33  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_483])).
% 2.51/1.33  tff(c_486, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_421])).
% 2.51/1.33  tff(c_490, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_486, c_359])).
% 2.51/1.33  tff(c_524, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_521, c_490])).
% 2.51/1.33  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_524])).
% 2.51/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  Inference rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Ref     : 0
% 2.51/1.33  #Sup     : 90
% 2.51/1.33  #Fact    : 2
% 2.51/1.33  #Define  : 0
% 2.51/1.33  #Split   : 3
% 2.51/1.33  #Chain   : 0
% 2.51/1.33  #Close   : 0
% 2.51/1.33  
% 2.51/1.33  Ordering : KBO
% 2.51/1.33  
% 2.51/1.33  Simplification rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Subsume      : 13
% 2.51/1.33  #Demod        : 32
% 2.51/1.33  #Tautology    : 22
% 2.51/1.33  #SimpNegUnit  : 3
% 2.51/1.33  #BackRed      : 10
% 2.51/1.33  
% 2.51/1.33  #Partial instantiations: 0
% 2.51/1.33  #Strategies tried      : 1
% 2.51/1.33  
% 2.51/1.33  Timing (in seconds)
% 2.51/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.27
% 2.51/1.33  Parsing              : 0.15
% 2.51/1.33  CNF conversion       : 0.02
% 2.51/1.33  Main loop            : 0.28
% 2.51/1.33  Inferencing          : 0.11
% 2.51/1.33  Reduction            : 0.07
% 2.51/1.33  Demodulation         : 0.05
% 2.51/1.33  BG Simplification    : 0.02
% 2.51/1.33  Subsumption          : 0.07
% 2.51/1.33  Abstraction          : 0.01
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.59
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
