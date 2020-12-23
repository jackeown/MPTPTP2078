%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 140 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_58,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),B_67)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_447,plain,(
    ! [C_99,D_100,A_101] :
      ( r2_hidden(C_99,D_100)
      | ~ r2_hidden(D_100,A_101)
      | ~ r2_hidden(C_99,k1_setfam_1(A_101))
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_462,plain,(
    ! [C_99] :
      ( r2_hidden(C_99,'#skF_7')
      | ~ r2_hidden(C_99,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_60,c_447])).

tff(c_498,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_423,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_436,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_7',B_98)
      | ~ r1_tarski('#skF_8',B_98) ) ),
    inference(resolution,[status(thm)],[c_60,c_423])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = A_55
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_258,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(A_78,B_79)
      | k4_xboole_0(k1_tarski(A_78),B_79) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_265,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,k1_xboole_0)
      | k1_tarski(A_78) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_258])).

tff(c_296,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,B_83)
      | ~ r2_hidden(C_84,A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_309,plain,(
    ! [C_85,A_86] :
      ( ~ r2_hidden(C_85,k1_xboole_0)
      | ~ r2_hidden(C_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_349,plain,(
    ! [A_88,A_89] :
      ( ~ r2_hidden(A_88,A_89)
      | k1_tarski(A_88) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_265,c_309])).

tff(c_365,plain,(
    ! [A_78] : k1_tarski(A_78) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_265,c_349])).

tff(c_152,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k1_tarski(A_69),B_70) = k1_xboole_0
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_159,plain,(
    ! [A_69] :
      ( k1_tarski(A_69) = k1_xboole_0
      | ~ r2_hidden(A_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_123])).

tff(c_370,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_159])).

tff(c_444,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_436,c_370])).

tff(c_500,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_444])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_500])).

tff(c_517,plain,(
    ! [C_105] :
      ( r2_hidden(C_105,'#skF_7')
      | ~ r2_hidden(C_105,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_1028,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_8'),B_162),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_162) ) ),
    inference(resolution,[status(thm)],[c_6,c_517])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1038,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1028,c_4])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_1038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:09:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.80/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.80/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.80/1.43  
% 2.80/1.44  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.80/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.44  tff(f_99, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.80/1.44  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.80/1.44  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.80/1.44  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.80/1.44  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.80/1.44  tff(c_58, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.44  tff(c_145, plain, (![A_66, B_67]: (~r2_hidden('#skF_1'(A_66, B_67), B_67) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.44  tff(c_150, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.80/1.44  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.44  tff(c_447, plain, (![C_99, D_100, A_101]: (r2_hidden(C_99, D_100) | ~r2_hidden(D_100, A_101) | ~r2_hidden(C_99, k1_setfam_1(A_101)) | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.44  tff(c_462, plain, (![C_99]: (r2_hidden(C_99, '#skF_7') | ~r2_hidden(C_99, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_60, c_447])).
% 2.80/1.44  tff(c_498, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_462])).
% 2.80/1.44  tff(c_423, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.44  tff(c_436, plain, (![B_98]: (r2_hidden('#skF_7', B_98) | ~r1_tarski('#skF_8', B_98))), inference(resolution, [status(thm)], [c_60, c_423])).
% 2.80/1.44  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.80/1.44  tff(c_115, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=A_55 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.44  tff(c_123, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(resolution, [status(thm)], [c_16, c_115])).
% 2.80/1.44  tff(c_258, plain, (![A_78, B_79]: (r2_hidden(A_78, B_79) | k4_xboole_0(k1_tarski(A_78), B_79)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.44  tff(c_265, plain, (![A_78]: (r2_hidden(A_78, k1_xboole_0) | k1_tarski(A_78)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123, c_258])).
% 2.80/1.44  tff(c_296, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, B_83) | ~r2_hidden(C_84, A_82))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.44  tff(c_309, plain, (![C_85, A_86]: (~r2_hidden(C_85, k1_xboole_0) | ~r2_hidden(C_85, A_86))), inference(resolution, [status(thm)], [c_16, c_296])).
% 2.80/1.44  tff(c_349, plain, (![A_88, A_89]: (~r2_hidden(A_88, A_89) | k1_tarski(A_88)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_265, c_309])).
% 2.80/1.44  tff(c_365, plain, (![A_78]: (k1_tarski(A_78)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_265, c_349])).
% 2.80/1.44  tff(c_152, plain, (![A_69, B_70]: (k4_xboole_0(k1_tarski(A_69), B_70)=k1_xboole_0 | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.44  tff(c_159, plain, (![A_69]: (k1_tarski(A_69)=k1_xboole_0 | ~r2_hidden(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_123])).
% 2.80/1.44  tff(c_370, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_365, c_159])).
% 2.80/1.44  tff(c_444, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_436, c_370])).
% 2.80/1.44  tff(c_500, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_444])).
% 2.80/1.44  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_500])).
% 2.80/1.44  tff(c_517, plain, (![C_105]: (r2_hidden(C_105, '#skF_7') | ~r2_hidden(C_105, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_462])).
% 2.80/1.44  tff(c_1028, plain, (![B_162]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_8'), B_162), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_162))), inference(resolution, [status(thm)], [c_6, c_517])).
% 2.80/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.44  tff(c_1038, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_1028, c_4])).
% 2.80/1.44  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_1038])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 2
% 2.80/1.44  #Sup     : 215
% 2.80/1.44  #Fact    : 4
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 2
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 51
% 2.80/1.44  #Demod        : 74
% 2.80/1.44  #Tautology    : 82
% 2.80/1.44  #SimpNegUnit  : 9
% 2.80/1.44  #BackRed      : 14
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.45  Preprocessing        : 0.32
% 2.80/1.45  Parsing              : 0.17
% 2.80/1.45  CNF conversion       : 0.02
% 2.80/1.45  Main loop            : 0.37
% 2.80/1.45  Inferencing          : 0.13
% 2.80/1.45  Reduction            : 0.11
% 2.80/1.45  Demodulation         : 0.07
% 2.80/1.45  BG Simplification    : 0.02
% 2.80/1.45  Subsumption          : 0.08
% 2.80/1.45  Abstraction          : 0.02
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.72
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
