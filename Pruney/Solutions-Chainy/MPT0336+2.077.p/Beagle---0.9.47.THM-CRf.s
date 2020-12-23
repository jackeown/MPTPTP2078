%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 212 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_60])).

tff(c_1013,plain,(
    ! [A_120,C_121,B_122] :
      ( ~ r1_xboole_0(A_120,C_121)
      | ~ r1_xboole_0(A_120,B_122)
      | r1_xboole_0(A_120,k2_xboole_0(B_122,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4574,plain,(
    ! [B_298,C_299,A_300] :
      ( r1_xboole_0(k2_xboole_0(B_298,C_299),A_300)
      | ~ r1_xboole_0(A_300,C_299)
      | ~ r1_xboole_0(A_300,B_298) ) ),
    inference(resolution,[status(thm)],[c_1013,c_4])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4603,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4574,c_42])).

tff(c_4615,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4603])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_422,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_463,plain,(
    ! [C_89] :
      ( ~ r2_hidden(C_89,'#skF_4')
      | ~ r2_hidden(C_89,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_422])).

tff(c_477,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_463])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | r1_xboole_0(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_666,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_xboole_0(A_101,C_102)
      | ~ r1_xboole_0(B_103,C_102)
      | ~ r1_tarski(A_101,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4729,plain,(
    ! [A_301,B_302,C_303,A_304] :
      ( r1_xboole_0(A_301,k3_xboole_0(B_302,C_303))
      | ~ r1_tarski(A_301,A_304)
      | ~ r1_xboole_0(A_304,B_302) ) ),
    inference(resolution,[status(thm)],[c_26,c_666])).

tff(c_5421,plain,(
    ! [B_331,C_332] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k3_xboole_0(B_331,C_332))
      | ~ r1_xboole_0(k1_tarski('#skF_6'),B_331) ) ),
    inference(resolution,[status(thm)],[c_49,c_4729])).

tff(c_332,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,(
    ! [B_27,A_26] : r1_xboole_0(B_27,k4_xboole_0(A_26,B_27)) ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_126,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_143,plain,(
    ! [B_27,A_26] : k4_xboole_0(B_27,k4_xboole_0(A_26,B_27)) = B_27 ),
    inference(resolution,[status(thm)],[c_65,c_126])).

tff(c_345,plain,(
    ! [B_84] : k3_xboole_0(B_84,B_84) = B_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_143])).

tff(c_277,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1430,plain,(
    ! [A_149,B_150,B_151] :
      ( ~ r1_xboole_0(A_149,B_150)
      | r1_xboole_0(k3_xboole_0(A_149,B_150),B_151) ) ),
    inference(resolution,[status(thm)],[c_277,c_14])).

tff(c_1453,plain,(
    ! [B_84,B_151] :
      ( ~ r1_xboole_0(B_84,B_84)
      | r1_xboole_0(B_84,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1430])).

tff(c_5465,plain,(
    ! [B_151] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_151)
      | ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5421,c_1453])).

tff(c_9654,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5465])).

tff(c_9667,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_9654])).

tff(c_9677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_9667])).

tff(c_9712,plain,(
    ! [B_441] : r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_441) ),
    inference(splitRight,[status(thm)],[c_5465])).

tff(c_374,plain,(
    ! [B_85] : k3_xboole_0(B_85,B_85) = B_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_143])).

tff(c_383,plain,(
    ! [B_85,C_14] :
      ( ~ r1_xboole_0(B_85,B_85)
      | ~ r2_hidden(C_14,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_14])).

tff(c_9916,plain,(
    ! [C_447] : ~ r2_hidden(C_447,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9712,c_383])).

tff(c_9928,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_9916])).

tff(c_9943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4615,c_9928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.42/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.74  
% 7.42/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.42/2.75  
% 7.42/2.75  %Foreground sorts:
% 7.42/2.75  
% 7.42/2.75  
% 7.42/2.75  %Background operators:
% 7.42/2.75  
% 7.42/2.75  
% 7.42/2.75  %Foreground operators:
% 7.42/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.42/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.42/2.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.42/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.42/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.42/2.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.42/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.42/2.75  tff('#skF_5', type, '#skF_5': $i).
% 7.42/2.75  tff('#skF_6', type, '#skF_6': $i).
% 7.42/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.42/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.42/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.42/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.42/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.42/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.42/2.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.42/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.42/2.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.42/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.42/2.75  
% 7.42/2.76  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.42/2.76  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.42/2.76  tff(f_87, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.42/2.76  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.42/2.76  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.42/2.76  tff(f_110, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.42/2.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.42/2.76  tff(f_93, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 7.42/2.76  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.42/2.76  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.42/2.76  tff(f_95, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.42/2.76  tff(f_99, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.42/2.76  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.42/2.76  tff(c_60, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.42/2.76  tff(c_66, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_60])).
% 7.42/2.76  tff(c_1013, plain, (![A_120, C_121, B_122]: (~r1_xboole_0(A_120, C_121) | ~r1_xboole_0(A_120, B_122) | r1_xboole_0(A_120, k2_xboole_0(B_122, C_121)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.42/2.76  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.42/2.76  tff(c_4574, plain, (![B_298, C_299, A_300]: (r1_xboole_0(k2_xboole_0(B_298, C_299), A_300) | ~r1_xboole_0(A_300, C_299) | ~r1_xboole_0(A_300, B_298))), inference(resolution, [status(thm)], [c_1013, c_4])).
% 7.42/2.76  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.42/2.76  tff(c_4603, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4574, c_42])).
% 7.42/2.76  tff(c_4615, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4603])).
% 7.42/2.76  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.42/2.76  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.42/2.76  tff(c_422, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.42/2.76  tff(c_463, plain, (![C_89]: (~r2_hidden(C_89, '#skF_4') | ~r2_hidden(C_89, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_422])).
% 7.42/2.76  tff(c_477, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_463])).
% 7.42/2.76  tff(c_40, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.42/2.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.42/2.76  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.42/2.76  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 7.42/2.76  tff(c_26, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | r1_xboole_0(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.42/2.76  tff(c_666, plain, (![A_101, C_102, B_103]: (r1_xboole_0(A_101, C_102) | ~r1_xboole_0(B_103, C_102) | ~r1_tarski(A_101, B_103))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.42/2.76  tff(c_4729, plain, (![A_301, B_302, C_303, A_304]: (r1_xboole_0(A_301, k3_xboole_0(B_302, C_303)) | ~r1_tarski(A_301, A_304) | ~r1_xboole_0(A_304, B_302))), inference(resolution, [status(thm)], [c_26, c_666])).
% 7.42/2.76  tff(c_5421, plain, (![B_331, C_332]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k3_xboole_0(B_331, C_332)) | ~r1_xboole_0(k1_tarski('#skF_6'), B_331))), inference(resolution, [status(thm)], [c_49, c_4729])).
% 7.42/2.76  tff(c_332, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.42/2.76  tff(c_28, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.42/2.76  tff(c_65, plain, (![B_27, A_26]: (r1_xboole_0(B_27, k4_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_28, c_60])).
% 7.42/2.76  tff(c_126, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.42/2.76  tff(c_143, plain, (![B_27, A_26]: (k4_xboole_0(B_27, k4_xboole_0(A_26, B_27))=B_27)), inference(resolution, [status(thm)], [c_65, c_126])).
% 7.42/2.76  tff(c_345, plain, (![B_84]: (k3_xboole_0(B_84, B_84)=B_84)), inference(superposition, [status(thm), theory('equality')], [c_332, c_143])).
% 7.42/2.76  tff(c_277, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.42/2.76  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.42/2.76  tff(c_1430, plain, (![A_149, B_150, B_151]: (~r1_xboole_0(A_149, B_150) | r1_xboole_0(k3_xboole_0(A_149, B_150), B_151))), inference(resolution, [status(thm)], [c_277, c_14])).
% 7.42/2.76  tff(c_1453, plain, (![B_84, B_151]: (~r1_xboole_0(B_84, B_84) | r1_xboole_0(B_84, B_151))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1430])).
% 7.42/2.76  tff(c_5465, plain, (![B_151]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_151) | ~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_5421, c_1453])).
% 7.42/2.76  tff(c_9654, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5465])).
% 7.42/2.76  tff(c_9667, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_9654])).
% 7.42/2.76  tff(c_9677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_9667])).
% 7.42/2.76  tff(c_9712, plain, (![B_441]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_441))), inference(splitRight, [status(thm)], [c_5465])).
% 7.42/2.76  tff(c_374, plain, (![B_85]: (k3_xboole_0(B_85, B_85)=B_85)), inference(superposition, [status(thm), theory('equality')], [c_332, c_143])).
% 7.42/2.76  tff(c_383, plain, (![B_85, C_14]: (~r1_xboole_0(B_85, B_85) | ~r2_hidden(C_14, B_85))), inference(superposition, [status(thm), theory('equality')], [c_374, c_14])).
% 7.42/2.76  tff(c_9916, plain, (![C_447]: (~r2_hidden(C_447, k3_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_9712, c_383])).
% 7.42/2.76  tff(c_9928, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_9916])).
% 7.42/2.76  tff(c_9943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4615, c_9928])).
% 7.42/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/2.76  
% 7.42/2.76  Inference rules
% 7.42/2.76  ----------------------
% 7.42/2.76  #Ref     : 0
% 7.42/2.76  #Sup     : 2446
% 7.42/2.76  #Fact    : 0
% 7.42/2.76  #Define  : 0
% 7.42/2.76  #Split   : 12
% 7.42/2.76  #Chain   : 0
% 7.42/2.76  #Close   : 0
% 7.42/2.76  
% 7.42/2.76  Ordering : KBO
% 7.42/2.76  
% 7.42/2.76  Simplification rules
% 7.42/2.76  ----------------------
% 7.42/2.76  #Subsume      : 431
% 7.42/2.76  #Demod        : 994
% 7.42/2.76  #Tautology    : 898
% 7.42/2.76  #SimpNegUnit  : 23
% 7.42/2.76  #BackRed      : 4
% 7.42/2.76  
% 7.42/2.76  #Partial instantiations: 0
% 7.42/2.76  #Strategies tried      : 1
% 7.42/2.76  
% 7.42/2.76  Timing (in seconds)
% 7.42/2.76  ----------------------
% 7.42/2.76  Preprocessing        : 0.33
% 7.42/2.76  Parsing              : 0.19
% 7.42/2.76  CNF conversion       : 0.02
% 7.42/2.76  Main loop            : 1.62
% 7.42/2.76  Inferencing          : 0.45
% 7.42/2.76  Reduction            : 0.61
% 7.42/2.76  Demodulation         : 0.46
% 7.42/2.76  BG Simplification    : 0.05
% 7.42/2.76  Subsumption          : 0.40
% 7.42/2.76  Abstraction          : 0.06
% 7.42/2.76  MUC search           : 0.00
% 7.42/2.76  Cooper               : 0.00
% 7.42/2.76  Total                : 1.98
% 7.42/2.76  Index Insertion      : 0.00
% 7.42/2.76  Index Deletion       : 0.00
% 7.42/2.76  Index Matching       : 0.00
% 7.42/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
