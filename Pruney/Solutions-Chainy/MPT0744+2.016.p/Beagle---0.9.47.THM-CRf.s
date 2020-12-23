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
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 19.04s
% Output     : CNFRefutation 19.04s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 205 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_78,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35199,plain,(
    ! [A_3310,B_3311] :
      ( r1_ordinal1(A_3310,B_3311)
      | ~ r1_tarski(A_3310,B_3311)
      | ~ v3_ordinal1(B_3311)
      | ~ v3_ordinal1(A_3310) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_35220,plain,(
    ! [B_3313] :
      ( r1_ordinal1(B_3313,B_3313)
      | ~ v3_ordinal1(B_3313) ) ),
    inference(resolution,[status(thm)],[c_26,c_35199])).

tff(c_72,plain,(
    ! [B_29] : r2_hidden(B_29,k1_ordinal1(B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_80,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_82,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_137,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_88])).

tff(c_663,plain,(
    ! [B_127,A_128] :
      ( r2_hidden(B_127,A_128)
      | r1_ordinal1(A_128,B_127)
      | ~ v3_ordinal1(B_127)
      | ~ v3_ordinal1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_138,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden(A_55,B_56)
      | r2_hidden(A_55,k1_ordinal1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_138,c_124])).

tff(c_752,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_663,c_148])).

tff(c_786,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_752])).

tff(c_68,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_ordinal1(A_26,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_852,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(A_136,B_137)
      | ~ r1_ordinal1(A_136,B_137)
      | ~ v3_ordinal1(B_137)
      | ~ v3_ordinal1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3999,plain,(
    ! [B_427,A_428] :
      ( B_427 = A_428
      | ~ r1_tarski(B_427,A_428)
      | ~ r1_ordinal1(A_428,B_427)
      | ~ v3_ordinal1(B_427)
      | ~ v3_ordinal1(A_428) ) ),
    inference(resolution,[status(thm)],[c_852,c_22])).

tff(c_34412,plain,(
    ! [B_3211,A_3212] :
      ( B_3211 = A_3212
      | ~ r1_ordinal1(B_3211,A_3212)
      | ~ r1_ordinal1(A_3212,B_3211)
      | ~ v3_ordinal1(B_3211)
      | ~ v3_ordinal1(A_3212) ) ),
    inference(resolution,[status(thm)],[c_68,c_3999])).

tff(c_34442,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_786,c_34412])).

tff(c_34462,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_137,c_34442])).

tff(c_34469,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34462,c_124])).

tff(c_34473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34469])).

tff(c_34474,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_34956,plain,(
    ! [B_3294,A_3295] :
      ( r2_hidden(B_3294,A_3295)
      | r1_ordinal1(A_3295,B_3294)
      | ~ v3_ordinal1(B_3294)
      | ~ v3_ordinal1(A_3295) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34475,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_34804,plain,(
    ! [B_3274,A_3275] :
      ( B_3274 = A_3275
      | r2_hidden(A_3275,B_3274)
      | ~ r2_hidden(A_3275,k1_ordinal1(B_3274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34815,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34475,c_34804])).

tff(c_34818,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34815])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34821,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_34818,c_2])).

tff(c_34971,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34956,c_34821])).

tff(c_35052,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_34971])).

tff(c_35054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34474,c_35052])).

tff(c_35055,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34815])).

tff(c_35059,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35055,c_34474])).

tff(c_35223,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_35220,c_35059])).

tff(c_35227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_35223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.04/10.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.04/10.40  
% 19.04/10.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.04/10.41  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 19.04/10.41  
% 19.04/10.41  %Foreground sorts:
% 19.04/10.41  
% 19.04/10.41  
% 19.04/10.41  %Background operators:
% 19.04/10.41  
% 19.04/10.41  
% 19.04/10.41  %Foreground operators:
% 19.04/10.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 19.04/10.41  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 19.04/10.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.04/10.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.04/10.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.04/10.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 19.04/10.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.04/10.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.04/10.41  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 19.04/10.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.04/10.41  tff('#skF_5', type, '#skF_5': $i).
% 19.04/10.41  tff('#skF_6', type, '#skF_6': $i).
% 19.04/10.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.04/10.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 19.04/10.41  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 19.04/10.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 19.04/10.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.04/10.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.04/10.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.04/10.41  
% 19.04/10.42  tff(f_104, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 19.04/10.42  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.04/10.42  tff(f_79, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 19.04/10.42  tff(f_85, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 19.04/10.42  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 19.04/10.42  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 19.04/10.42  tff(c_78, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.04/10.42  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.04/10.42  tff(c_35199, plain, (![A_3310, B_3311]: (r1_ordinal1(A_3310, B_3311) | ~r1_tarski(A_3310, B_3311) | ~v3_ordinal1(B_3311) | ~v3_ordinal1(A_3310))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.04/10.42  tff(c_35220, plain, (![B_3313]: (r1_ordinal1(B_3313, B_3313) | ~v3_ordinal1(B_3313))), inference(resolution, [status(thm)], [c_26, c_35199])).
% 19.04/10.42  tff(c_72, plain, (![B_29]: (r2_hidden(B_29, k1_ordinal1(B_29)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.04/10.42  tff(c_80, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.04/10.42  tff(c_82, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.04/10.42  tff(c_124, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_82])).
% 19.04/10.42  tff(c_88, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.04/10.42  tff(c_137, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_124, c_88])).
% 19.04/10.42  tff(c_663, plain, (![B_127, A_128]: (r2_hidden(B_127, A_128) | r1_ordinal1(A_128, B_127) | ~v3_ordinal1(B_127) | ~v3_ordinal1(A_128))), inference(cnfTransformation, [status(thm)], [f_94])).
% 19.04/10.42  tff(c_138, plain, (![A_55, B_56]: (~r2_hidden(A_55, B_56) | r2_hidden(A_55, k1_ordinal1(B_56)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.04/10.42  tff(c_148, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_138, c_124])).
% 19.04/10.42  tff(c_752, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_663, c_148])).
% 19.04/10.42  tff(c_786, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_80, c_752])).
% 19.04/10.42  tff(c_68, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~r1_ordinal1(A_26, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.04/10.42  tff(c_852, plain, (![A_136, B_137]: (r1_tarski(A_136, B_137) | ~r1_ordinal1(A_136, B_137) | ~v3_ordinal1(B_137) | ~v3_ordinal1(A_136))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.04/10.42  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.04/10.42  tff(c_3999, plain, (![B_427, A_428]: (B_427=A_428 | ~r1_tarski(B_427, A_428) | ~r1_ordinal1(A_428, B_427) | ~v3_ordinal1(B_427) | ~v3_ordinal1(A_428))), inference(resolution, [status(thm)], [c_852, c_22])).
% 19.04/10.42  tff(c_34412, plain, (![B_3211, A_3212]: (B_3211=A_3212 | ~r1_ordinal1(B_3211, A_3212) | ~r1_ordinal1(A_3212, B_3211) | ~v3_ordinal1(B_3211) | ~v3_ordinal1(A_3212))), inference(resolution, [status(thm)], [c_68, c_3999])).
% 19.04/10.42  tff(c_34442, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_786, c_34412])).
% 19.04/10.42  tff(c_34462, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_137, c_34442])).
% 19.04/10.42  tff(c_34469, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34462, c_124])).
% 19.04/10.42  tff(c_34473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_34469])).
% 19.04/10.42  tff(c_34474, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 19.04/10.42  tff(c_34956, plain, (![B_3294, A_3295]: (r2_hidden(B_3294, A_3295) | r1_ordinal1(A_3295, B_3294) | ~v3_ordinal1(B_3294) | ~v3_ordinal1(A_3295))), inference(cnfTransformation, [status(thm)], [f_94])).
% 19.04/10.42  tff(c_34475, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_82])).
% 19.04/10.42  tff(c_34804, plain, (![B_3274, A_3275]: (B_3274=A_3275 | r2_hidden(A_3275, B_3274) | ~r2_hidden(A_3275, k1_ordinal1(B_3274)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 19.04/10.42  tff(c_34815, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34475, c_34804])).
% 19.04/10.42  tff(c_34818, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_34815])).
% 19.04/10.42  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 19.04/10.42  tff(c_34821, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_34818, c_2])).
% 19.04/10.42  tff(c_34971, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_34956, c_34821])).
% 19.04/10.42  tff(c_35052, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_34971])).
% 19.04/10.42  tff(c_35054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34474, c_35052])).
% 19.04/10.42  tff(c_35055, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_34815])).
% 19.04/10.42  tff(c_35059, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35055, c_34474])).
% 19.04/10.42  tff(c_35223, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_35220, c_35059])).
% 19.04/10.42  tff(c_35227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_35223])).
% 19.04/10.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.04/10.42  
% 19.04/10.42  Inference rules
% 19.04/10.42  ----------------------
% 19.04/10.42  #Ref     : 0
% 19.04/10.42  #Sup     : 7496
% 19.04/10.42  #Fact    : 62
% 19.04/10.42  #Define  : 0
% 19.04/10.42  #Split   : 3
% 19.04/10.42  #Chain   : 0
% 19.04/10.42  #Close   : 0
% 19.04/10.42  
% 19.04/10.42  Ordering : KBO
% 19.04/10.42  
% 19.04/10.42  Simplification rules
% 19.04/10.42  ----------------------
% 19.04/10.42  #Subsume      : 2486
% 19.04/10.42  #Demod        : 524
% 19.04/10.42  #Tautology    : 105
% 19.04/10.42  #SimpNegUnit  : 155
% 19.04/10.42  #BackRed      : 11
% 19.04/10.42  
% 19.04/10.42  #Partial instantiations: 0
% 19.04/10.42  #Strategies tried      : 1
% 19.04/10.42  
% 19.04/10.42  Timing (in seconds)
% 19.04/10.42  ----------------------
% 19.04/10.42  Preprocessing        : 0.32
% 19.04/10.42  Parsing              : 0.16
% 19.04/10.42  CNF conversion       : 0.03
% 19.04/10.42  Main loop            : 9.32
% 19.04/10.42  Inferencing          : 1.43
% 19.04/10.42  Reduction            : 2.86
% 19.04/10.42  Demodulation         : 1.15
% 19.04/10.42  BG Simplification    : 0.14
% 19.04/10.42  Subsumption          : 4.23
% 19.04/10.42  Abstraction          : 0.22
% 19.04/10.42  MUC search           : 0.00
% 19.04/10.42  Cooper               : 0.00
% 19.04/10.42  Total                : 9.67
% 19.04/10.42  Index Insertion      : 0.00
% 19.04/10.42  Index Deletion       : 0.00
% 19.04/10.42  Index Matching       : 0.00
% 19.04/10.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
