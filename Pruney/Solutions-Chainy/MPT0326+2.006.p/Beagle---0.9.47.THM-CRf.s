%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 260 expanded)
%              Number of equality atoms :   25 (  68 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_416,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_445,plain,(
    ! [A_98,B_99] :
      ( ~ v1_xboole_0(A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_416,c_2])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_453,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_445,c_32])).

tff(c_121,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_144,c_32])).

tff(c_34,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_7','#skF_6'))
    | r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_287,plain,(
    ! [B_74,D_75,A_76,C_77] :
      ( r1_tarski(B_74,D_75)
      | k2_zfmisc_1(A_76,B_74) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_76,B_74),k2_zfmisc_1(C_77,D_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_297,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_287])).

tff(c_315,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_297])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k1_xboole_0 = B_19
      | k1_xboole_0 = A_18
      | k2_zfmisc_1(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_336,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_22])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_37,C_38] :
      ( ~ r1_xboole_0(A_37,A_37)
      | ~ r2_hidden(C_38,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_94,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_90])).

tff(c_99,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_346,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_99])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_346])).

tff(c_354,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_365,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_99])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_365])).

tff(c_373,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_529,plain,(
    ! [A_109,C_110,B_111,D_112] :
      ( r1_tarski(A_109,C_110)
      | k2_zfmisc_1(A_109,B_111) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_109,B_111),k2_zfmisc_1(C_110,D_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_539,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k2_zfmisc_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_373,c_529])).

tff(c_557,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_539])).

tff(c_578,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_22])).

tff(c_580,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_386,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_395,plain,(
    ! [A_83,C_84] :
      ( ~ r1_xboole_0(A_83,A_83)
      | ~ r2_hidden(C_84,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_386])).

tff(c_399,plain,(
    ! [C_85] : ~ r2_hidden(C_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_395])).

tff(c_404,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_399])).

tff(c_586,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_404])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_586])).

tff(c_595,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_623,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_404])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.39  
% 2.29/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.29/1.39  
% 2.29/1.39  %Foreground sorts:
% 2.29/1.39  
% 2.29/1.39  
% 2.29/1.39  %Background operators:
% 2.29/1.39  
% 2.29/1.39  
% 2.29/1.39  %Foreground operators:
% 2.29/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.29/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.29/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.29/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.39  
% 2.61/1.40  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.61/1.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.61/1.40  tff(f_80, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.61/1.40  tff(f_72, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.61/1.40  tff(f_66, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.61/1.40  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.40  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.40  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.40  tff(c_416, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.40  tff(c_445, plain, (![A_98, B_99]: (~v1_xboole_0(A_98) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_416, c_2])).
% 2.61/1.40  tff(c_32, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.40  tff(c_453, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_445, c_32])).
% 2.61/1.40  tff(c_121, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.61/1.40  tff(c_144, plain, (![A_51, B_52]: (~v1_xboole_0(A_51) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_121, c_2])).
% 2.61/1.40  tff(c_148, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_144, c_32])).
% 2.61/1.40  tff(c_34, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_7', '#skF_6')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.40  tff(c_80, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.61/1.40  tff(c_287, plain, (![B_74, D_75, A_76, C_77]: (r1_tarski(B_74, D_75) | k2_zfmisc_1(A_76, B_74)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_76, B_74), k2_zfmisc_1(C_77, D_75)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.40  tff(c_297, plain, (r1_tarski('#skF_5', '#skF_7') | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_287])).
% 2.61/1.40  tff(c_315, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32, c_297])).
% 2.61/1.40  tff(c_22, plain, (![B_19, A_18]: (k1_xboole_0=B_19 | k1_xboole_0=A_18 | k2_zfmisc_1(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.40  tff(c_336, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_315, c_22])).
% 2.61/1.40  tff(c_338, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_336])).
% 2.61/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.40  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.61/1.40  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.61/1.40  tff(c_81, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.61/1.40  tff(c_90, plain, (![A_37, C_38]: (~r1_xboole_0(A_37, A_37) | ~r2_hidden(C_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_12, c_81])).
% 2.61/1.40  tff(c_94, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_90])).
% 2.61/1.40  tff(c_99, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_94])).
% 2.61/1.40  tff(c_346, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_99])).
% 2.61/1.40  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_346])).
% 2.61/1.40  tff(c_354, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_336])).
% 2.61/1.40  tff(c_365, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_99])).
% 2.61/1.40  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_365])).
% 2.61/1.40  tff(c_373, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 2.61/1.40  tff(c_529, plain, (![A_109, C_110, B_111, D_112]: (r1_tarski(A_109, C_110) | k2_zfmisc_1(A_109, B_111)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_109, B_111), k2_zfmisc_1(C_110, D_112)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.40  tff(c_539, plain, (r1_tarski('#skF_5', '#skF_7') | k2_zfmisc_1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_373, c_529])).
% 2.61/1.40  tff(c_557, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32, c_539])).
% 2.61/1.40  tff(c_578, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_557, c_22])).
% 2.61/1.40  tff(c_580, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_578])).
% 2.61/1.40  tff(c_386, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.61/1.40  tff(c_395, plain, (![A_83, C_84]: (~r1_xboole_0(A_83, A_83) | ~r2_hidden(C_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_12, c_386])).
% 2.61/1.40  tff(c_399, plain, (![C_85]: (~r2_hidden(C_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_395])).
% 2.61/1.40  tff(c_404, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_399])).
% 2.61/1.40  tff(c_586, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_404])).
% 2.61/1.40  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_453, c_586])).
% 2.61/1.40  tff(c_595, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_578])).
% 2.61/1.40  tff(c_623, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_595, c_404])).
% 2.61/1.40  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_623])).
% 2.61/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  Inference rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Ref     : 0
% 2.61/1.40  #Sup     : 115
% 2.61/1.40  #Fact    : 0
% 2.61/1.40  #Define  : 0
% 2.61/1.40  #Split   : 3
% 2.61/1.40  #Chain   : 0
% 2.61/1.40  #Close   : 0
% 2.61/1.40  
% 2.61/1.40  Ordering : KBO
% 2.61/1.40  
% 2.61/1.40  Simplification rules
% 2.61/1.40  ----------------------
% 2.61/1.40  #Subsume      : 11
% 2.61/1.40  #Demod        : 114
% 2.61/1.40  #Tautology    : 52
% 2.61/1.40  #SimpNegUnit  : 6
% 2.61/1.40  #BackRed      : 54
% 2.61/1.40  
% 2.61/1.40  #Partial instantiations: 0
% 2.61/1.40  #Strategies tried      : 1
% 2.61/1.40  
% 2.61/1.40  Timing (in seconds)
% 2.61/1.40  ----------------------
% 2.61/1.41  Preprocessing        : 0.30
% 2.61/1.41  Parsing              : 0.17
% 2.61/1.41  CNF conversion       : 0.02
% 2.61/1.41  Main loop            : 0.28
% 2.61/1.41  Inferencing          : 0.10
% 2.61/1.41  Reduction            : 0.08
% 2.61/1.41  Demodulation         : 0.06
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.05
% 2.61/1.41  Abstraction          : 0.01
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.61
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.41  Index Matching       : 0.00
% 2.61/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
