%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:16 EST 2020

% Result     : Theorem 30.37s
% Output     : CNFRefutation 30.37s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 234 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_77,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_48,plain,(
    ! [B_20] : r2_hidden(B_20,k1_ordinal1(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_484,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | r1_ordinal1(A_82,B_81)
      | ~ v3_ordinal1(B_81)
      | ~ v3_ordinal1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | r2_hidden(A_35,k1_ordinal1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_109,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_84])).

tff(c_565,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_484,c_109])).

tff(c_605,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_565])).

tff(c_64,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_94,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_64])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_421,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ r1_ordinal1(A_73,B_74)
      | ~ v3_ordinal1(B_74)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5470,plain,(
    ! [B_2459,A_2460] :
      ( B_2459 = A_2460
      | ~ r1_tarski(B_2459,A_2460)
      | ~ r1_ordinal1(A_2460,B_2459)
      | ~ v3_ordinal1(B_2459)
      | ~ v3_ordinal1(A_2460) ) ),
    inference(resolution,[status(thm)],[c_421,c_22])).

tff(c_60882,plain,(
    ! [B_16297,A_16298] :
      ( B_16297 = A_16298
      | ~ r1_ordinal1(B_16297,A_16298)
      | ~ r1_ordinal1(A_16298,B_16297)
      | ~ v3_ordinal1(B_16297)
      | ~ v3_ordinal1(A_16298) ) ),
    inference(resolution,[status(thm)],[c_44,c_5470])).

tff(c_60912,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_60882])).

tff(c_60932,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_605,c_60912])).

tff(c_60943,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60932,c_84])).

tff(c_60947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_60943])).

tff(c_60948,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_61389,plain,(
    ! [B_16362,A_16363] :
      ( r2_hidden(B_16362,A_16363)
      | r1_ordinal1(A_16363,B_16362)
      | ~ v3_ordinal1(B_16362)
      | ~ v3_ordinal1(A_16363) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60949,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_61278,plain,(
    ! [B_16350,A_16351] :
      ( B_16350 = A_16351
      | r2_hidden(A_16351,B_16350)
      | ~ r2_hidden(A_16351,k1_ordinal1(B_16350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61289,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60949,c_61278])).

tff(c_61292,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_61289])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61295,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_61292,c_2])).

tff(c_61412,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_61389,c_61295])).

tff(c_61503,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_61412])).

tff(c_61505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60948,c_61503])).

tff(c_61506,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_61289])).

tff(c_61510,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61506,c_60948])).

tff(c_61612,plain,(
    ! [B_16374,A_16375] :
      ( r2_hidden(B_16374,A_16375)
      | r1_ordinal1(A_16375,B_16374)
      | ~ v3_ordinal1(B_16374)
      | ~ v3_ordinal1(A_16375) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61507,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_61289])).

tff(c_61518,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61506,c_61507])).

tff(c_61635,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_61612,c_61518])).

tff(c_61723,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_61635])).

tff(c_61725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61510,c_61723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:31:50 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.37/20.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.37/20.06  
% 30.37/20.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.37/20.06  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 30.37/20.06  
% 30.37/20.06  %Foreground sorts:
% 30.37/20.06  
% 30.37/20.06  
% 30.37/20.06  %Background operators:
% 30.37/20.06  
% 30.37/20.06  
% 30.37/20.06  %Foreground operators:
% 30.37/20.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 30.37/20.06  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 30.37/20.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.37/20.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.37/20.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.37/20.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 30.37/20.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.37/20.06  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 30.37/20.06  tff('#skF_5', type, '#skF_5': $i).
% 30.37/20.06  tff('#skF_6', type, '#skF_6': $i).
% 30.37/20.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.37/20.06  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 30.37/20.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.37/20.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.37/20.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.37/20.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 30.37/20.06  
% 30.37/20.07  tff(f_68, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 30.37/20.07  tff(f_87, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 30.37/20.07  tff(f_77, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 30.37/20.07  tff(f_62, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 30.37/20.07  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.37/20.07  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 30.37/20.07  tff(c_48, plain, (![B_20]: (r2_hidden(B_20, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.37/20.07  tff(c_54, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.37/20.07  tff(c_56, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.37/20.07  tff(c_484, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | r1_ordinal1(A_82, B_81) | ~v3_ordinal1(B_81) | ~v3_ordinal1(A_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.37/20.07  tff(c_95, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | r2_hidden(A_35, k1_ordinal1(B_36)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.37/20.07  tff(c_58, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.37/20.07  tff(c_84, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_58])).
% 30.37/20.07  tff(c_109, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_95, c_84])).
% 30.37/20.07  tff(c_565, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_484, c_109])).
% 30.37/20.07  tff(c_605, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_565])).
% 30.37/20.07  tff(c_64, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 30.37/20.07  tff(c_94, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_84, c_64])).
% 30.37/20.07  tff(c_44, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 30.37/20.07  tff(c_421, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~r1_ordinal1(A_73, B_74) | ~v3_ordinal1(B_74) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 30.37/20.07  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.37/20.07  tff(c_5470, plain, (![B_2459, A_2460]: (B_2459=A_2460 | ~r1_tarski(B_2459, A_2460) | ~r1_ordinal1(A_2460, B_2459) | ~v3_ordinal1(B_2459) | ~v3_ordinal1(A_2460))), inference(resolution, [status(thm)], [c_421, c_22])).
% 30.37/20.07  tff(c_60882, plain, (![B_16297, A_16298]: (B_16297=A_16298 | ~r1_ordinal1(B_16297, A_16298) | ~r1_ordinal1(A_16298, B_16297) | ~v3_ordinal1(B_16297) | ~v3_ordinal1(A_16298))), inference(resolution, [status(thm)], [c_44, c_5470])).
% 30.37/20.07  tff(c_60912, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_60882])).
% 30.37/20.07  tff(c_60932, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_605, c_60912])).
% 30.37/20.07  tff(c_60943, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60932, c_84])).
% 30.37/20.07  tff(c_60947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_60943])).
% 30.37/20.07  tff(c_60948, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 30.37/20.07  tff(c_61389, plain, (![B_16362, A_16363]: (r2_hidden(B_16362, A_16363) | r1_ordinal1(A_16363, B_16362) | ~v3_ordinal1(B_16362) | ~v3_ordinal1(A_16363))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.37/20.07  tff(c_60949, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_58])).
% 30.37/20.07  tff(c_61278, plain, (![B_16350, A_16351]: (B_16350=A_16351 | r2_hidden(A_16351, B_16350) | ~r2_hidden(A_16351, k1_ordinal1(B_16350)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.37/20.07  tff(c_61289, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60949, c_61278])).
% 30.37/20.07  tff(c_61292, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_61289])).
% 30.37/20.07  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 30.37/20.07  tff(c_61295, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_61292, c_2])).
% 30.37/20.07  tff(c_61412, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_61389, c_61295])).
% 30.37/20.07  tff(c_61503, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_61412])).
% 30.37/20.07  tff(c_61505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60948, c_61503])).
% 30.37/20.07  tff(c_61506, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_61289])).
% 30.37/20.07  tff(c_61510, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_61506, c_60948])).
% 30.37/20.07  tff(c_61612, plain, (![B_16374, A_16375]: (r2_hidden(B_16374, A_16375) | r1_ordinal1(A_16375, B_16374) | ~v3_ordinal1(B_16374) | ~v3_ordinal1(A_16375))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.37/20.07  tff(c_61507, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_61289])).
% 30.37/20.07  tff(c_61518, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_61506, c_61507])).
% 30.37/20.07  tff(c_61635, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_61612, c_61518])).
% 30.37/20.07  tff(c_61723, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_61635])).
% 30.37/20.07  tff(c_61725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61510, c_61723])).
% 30.37/20.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.37/20.07  
% 30.37/20.07  Inference rules
% 30.37/20.07  ----------------------
% 30.37/20.07  #Ref     : 0
% 30.37/20.07  #Sup     : 12520
% 30.37/20.07  #Fact    : 54
% 30.37/20.07  #Define  : 0
% 30.37/20.07  #Split   : 9
% 30.37/20.07  #Chain   : 0
% 30.37/20.07  #Close   : 0
% 30.37/20.07  
% 30.37/20.07  Ordering : KBO
% 30.37/20.07  
% 30.37/20.07  Simplification rules
% 30.37/20.07  ----------------------
% 30.37/20.07  #Subsume      : 4484
% 30.37/20.07  #Demod        : 710
% 30.37/20.07  #Tautology    : 348
% 30.37/20.07  #SimpNegUnit  : 214
% 30.37/20.07  #BackRed      : 17
% 30.37/20.07  
% 30.37/20.07  #Partial instantiations: 8775
% 30.37/20.07  #Strategies tried      : 1
% 30.37/20.07  
% 30.37/20.07  Timing (in seconds)
% 30.37/20.07  ----------------------
% 30.37/20.07  Preprocessing        : 0.32
% 30.37/20.07  Parsing              : 0.17
% 30.37/20.07  CNF conversion       : 0.03
% 30.37/20.07  Main loop            : 18.95
% 30.37/20.07  Inferencing          : 2.19
% 30.37/20.07  Reduction            : 6.36
% 30.37/20.07  Demodulation         : 1.63
% 30.37/20.08  BG Simplification    : 0.23
% 30.37/20.08  Subsumption          : 9.18
% 30.37/20.08  Abstraction          : 0.43
% 30.37/20.08  MUC search           : 0.00
% 30.37/20.08  Cooper               : 0.00
% 30.37/20.08  Total                : 19.31
% 30.37/20.08  Index Insertion      : 0.00
% 30.37/20.08  Index Deletion       : 0.00
% 30.37/20.08  Index Matching       : 0.00
% 30.37/20.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
