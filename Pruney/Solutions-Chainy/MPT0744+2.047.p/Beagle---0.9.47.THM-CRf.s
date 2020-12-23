%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 133 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 277 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_56,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_ordinal1(A)
      & v2_ordinal1(A)
      & v3_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_ordinal1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_44,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_11,B_12] :
      ( r1_ordinal1(A_11,A_11)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_266,plain,(
    ! [B_12] : ~ v3_ordinal1(B_12) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_20,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_20])).

tff(c_271,plain,(
    ! [A_11] :
      ( r1_ordinal1(A_11,A_11)
      | ~ v3_ordinal1(A_11) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_38,plain,(
    ! [B_15] : r2_hidden(B_15,k1_ordinal1(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_98,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54])).

tff(c_30,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_ordinal1(A_9,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ! [A_22] :
      ( v1_ordinal1(A_22)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r2_xboole_0(A_41,B_42)
      | ~ v3_ordinal1(B_42)
      | ~ v1_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_192,plain,(
    ! [A_48,B_49] :
      ( r2_hidden(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v1_ordinal1(A_48)
      | B_49 = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_100,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | r2_hidden(A_29,k1_ordinal1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_72])).

tff(c_202,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_104])).

tff(c_210,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44,c_202])).

tff(c_214,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_217,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_98,c_217])).

tff(c_222,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_226,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_72])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_226])).

tff(c_233,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_70,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_234,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_304,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | r2_hidden(A_65,B_64)
      | ~ r2_hidden(A_65,k1_ordinal1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_320,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_234,c_304])).

tff(c_323,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_14,plain,(
    ! [B_8,A_5] :
      ( r1_tarski(B_8,A_5)
      | ~ r2_hidden(B_8,A_5)
      | ~ v1_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_326,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_323,c_14])).

tff(c_329,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_326])).

tff(c_336,plain,(
    ! [A_68,B_69] :
      ( r1_ordinal1(A_68,B_69)
      | ~ r1_tarski(A_68,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_342,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_336])).

tff(c_349,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_342])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_349])).

tff(c_352,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_357,plain,(
    ~ r1_ordinal1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_233])).

tff(c_370,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_357])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.92  
% 2.86/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.93  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.86/1.93  
% 2.86/1.93  %Foreground sorts:
% 2.86/1.93  
% 2.86/1.93  
% 2.86/1.93  %Background operators:
% 2.86/1.93  
% 2.86/1.93  
% 2.86/1.93  %Foreground operators:
% 2.86/1.93  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.86/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.93  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.86/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.93  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.86/1.93  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.93  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.93  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.86/1.93  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.86/1.93  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.86/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.93  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.93  
% 2.86/1.95  tff(f_97, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 2.86/1.95  tff(f_70, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => r1_ordinal1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_ordinal1)).
% 2.86/1.95  tff(f_56, axiom, (?[A]: (((~v1_xboole_0(A) & v1_ordinal1(A)) & v2_ordinal1(A)) & v3_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_ordinal1)).
% 2.86/1.95  tff(f_78, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.86/1.95  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.86/1.95  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.86/1.95  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.86/1.95  tff(f_87, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.86/1.95  tff(f_47, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.86/1.95  tff(c_44, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.95  tff(c_32, plain, (![A_11, B_12]: (r1_ordinal1(A_11, A_11) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.86/1.95  tff(c_266, plain, (![B_12]: (~v3_ordinal1(B_12))), inference(splitLeft, [status(thm)], [c_32])).
% 2.86/1.95  tff(c_20, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.95  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_20])).
% 2.86/1.95  tff(c_271, plain, (![A_11]: (r1_ordinal1(A_11, A_11) | ~v3_ordinal1(A_11))), inference(splitRight, [status(thm)], [c_32])).
% 2.86/1.95  tff(c_38, plain, (![B_15]: (r2_hidden(B_15, k1_ordinal1(B_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.95  tff(c_46, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.95  tff(c_48, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.95  tff(c_72, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.86/1.95  tff(c_54, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.95  tff(c_98, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_54])).
% 2.86/1.95  tff(c_30, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r1_ordinal1(A_9, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.95  tff(c_58, plain, (![A_22]: (v1_ordinal1(A_22) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.95  tff(c_71, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.86/1.95  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.95  tff(c_157, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r2_xboole_0(A_41, B_42) | ~v3_ordinal1(B_42) | ~v1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.86/1.95  tff(c_192, plain, (![A_48, B_49]: (r2_hidden(A_48, B_49) | ~v3_ordinal1(B_49) | ~v1_ordinal1(A_48) | B_49=A_48 | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_2, c_157])).
% 2.86/1.95  tff(c_100, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | r2_hidden(A_29, k1_ordinal1(B_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.95  tff(c_104, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_100, c_72])).
% 2.86/1.95  tff(c_202, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_192, c_104])).
% 2.86/1.95  tff(c_210, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_44, c_202])).
% 2.86/1.95  tff(c_214, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_210])).
% 2.86/1.95  tff(c_217, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_214])).
% 2.86/1.95  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_98, c_217])).
% 2.86/1.95  tff(c_222, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_210])).
% 2.86/1.95  tff(c_226, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_72])).
% 2.86/1.95  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_226])).
% 2.86/1.95  tff(c_233, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.86/1.95  tff(c_70, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_58])).
% 2.86/1.95  tff(c_234, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 2.86/1.95  tff(c_304, plain, (![B_64, A_65]: (B_64=A_65 | r2_hidden(A_65, B_64) | ~r2_hidden(A_65, k1_ordinal1(B_64)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.95  tff(c_320, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_234, c_304])).
% 2.86/1.95  tff(c_323, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_320])).
% 2.86/1.95  tff(c_14, plain, (![B_8, A_5]: (r1_tarski(B_8, A_5) | ~r2_hidden(B_8, A_5) | ~v1_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.95  tff(c_326, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_323, c_14])).
% 2.86/1.95  tff(c_329, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_326])).
% 2.86/1.95  tff(c_336, plain, (![A_68, B_69]: (r1_ordinal1(A_68, B_69) | ~r1_tarski(A_68, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.95  tff(c_342, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_336])).
% 2.86/1.95  tff(c_349, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_342])).
% 2.86/1.95  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_349])).
% 2.86/1.95  tff(c_352, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_320])).
% 2.86/1.95  tff(c_357, plain, (~r1_ordinal1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_233])).
% 2.86/1.95  tff(c_370, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_271, c_357])).
% 2.86/1.95  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_370])).
% 2.86/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.95  
% 2.86/1.95  Inference rules
% 2.86/1.95  ----------------------
% 2.86/1.95  #Ref     : 0
% 2.86/1.95  #Sup     : 53
% 2.86/1.95  #Fact    : 0
% 2.86/1.95  #Define  : 0
% 2.86/1.95  #Split   : 7
% 2.86/1.95  #Chain   : 0
% 2.86/1.95  #Close   : 0
% 2.86/1.95  
% 2.86/1.95  Ordering : KBO
% 2.86/1.95  
% 2.86/1.95  Simplification rules
% 2.86/1.95  ----------------------
% 2.86/1.95  #Subsume      : 7
% 2.86/1.95  #Demod        : 32
% 2.86/1.95  #Tautology    : 31
% 2.86/1.95  #SimpNegUnit  : 9
% 2.86/1.95  #BackRed      : 17
% 2.86/1.95  
% 2.86/1.95  #Partial instantiations: 0
% 2.86/1.95  #Strategies tried      : 1
% 2.86/1.95  
% 2.86/1.95  Timing (in seconds)
% 2.86/1.95  ----------------------
% 2.86/1.96  Preprocessing        : 0.50
% 2.86/1.96  Parsing              : 0.27
% 2.86/1.96  CNF conversion       : 0.04
% 2.86/1.96  Main loop            : 0.48
% 2.86/1.96  Inferencing          : 0.18
% 2.86/1.96  Reduction            : 0.15
% 2.86/1.96  Demodulation         : 0.11
% 2.86/1.96  BG Simplification    : 0.02
% 2.86/1.96  Subsumption          : 0.08
% 2.86/1.96  Abstraction          : 0.02
% 2.86/1.96  MUC search           : 0.00
% 2.86/1.96  Cooper               : 0.00
% 2.86/1.96  Total                : 1.03
% 2.86/1.96  Index Insertion      : 0.00
% 2.86/1.96  Index Deletion       : 0.00
% 2.86/1.96  Index Matching       : 0.00
% 2.86/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
