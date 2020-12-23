%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 134 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 269 expanded)
%              Number of equality atoms :   17 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_xboole_0(A_12,B_13)
      | B_13 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_232,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_hidden(k4_tarski(A_75,B_76),k2_zfmisc_1(C_77,D_78))
      | ~ r2_hidden(B_76,D_78)
      | ~ r2_hidden(A_75,C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_173,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( r2_hidden(A_59,C_60)
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1(C_60,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    ! [A_59,B_61] :
      ( r2_hidden(A_59,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_173])).

tff(c_252,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,'#skF_5')
      | ~ r2_hidden(B_76,'#skF_5')
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_232,c_176])).

tff(c_269,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_285,plain,(
    ! [B_82] : r1_tarski('#skF_5',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    ! [D_46,A_47] :
      ( ~ r2_hidden(D_46,k1_xboole_0)
      | ~ r2_hidden(D_46,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_106])).

tff(c_148,plain,(
    ! [A_55,A_56] :
      ( ~ r2_hidden('#skF_4'(A_55,k1_xboole_0),A_56)
      | ~ r2_xboole_0(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_154,plain,(
    ! [A_57] : ~ r2_xboole_0(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_159,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_291,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_285,c_159])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_291])).

tff(c_298,plain,(
    ! [A_83] :
      ( r2_hidden(A_83,'#skF_5')
      | ~ r2_hidden(A_83,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15),A_14)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_344,plain,(
    ! [B_87] :
      ( ~ r2_xboole_0('#skF_5',B_87)
      | ~ r2_hidden('#skF_4'('#skF_5',B_87),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_298,c_32])).

tff(c_354,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_344])).

tff(c_357,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_354])).

tff(c_360,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_357])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_144,plain,(
    ! [B_51,D_52,A_53,C_54] :
      ( r2_hidden(B_51,D_52)
      | ~ r2_hidden(k4_tarski(A_53,B_51),k2_zfmisc_1(C_54,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_147,plain,(
    ! [B_51,A_53] :
      ( r2_hidden(B_51,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_53,B_51),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_253,plain,(
    ! [B_76,A_75] :
      ( r2_hidden(B_76,'#skF_6')
      | ~ r2_hidden(B_76,'#skF_5')
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_232,c_147])).

tff(c_424,plain,(
    ! [A_96] : ~ r2_hidden(A_96,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_448,plain,(
    ! [B_97] : r1_tarski('#skF_6',B_97) ),
    inference(resolution,[status(thm)],[c_6,c_424])).

tff(c_457,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_448,c_159])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_457])).

tff(c_510,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_6')
      | ~ r2_hidden(B_100,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_537,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'('#skF_5',B_101),'#skF_6')
      | r1_tarski('#skF_5',B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_510])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_547,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_537,c_4])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_360,c_547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:42:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.34  
% 2.49/1.34  %Foreground sorts:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Background operators:
% 2.49/1.34  
% 2.49/1.34  
% 2.49/1.34  %Foreground operators:
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.34  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.49/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.49/1.34  
% 2.49/1.35  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.49/1.35  tff(f_49, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.49/1.35  tff(f_59, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.49/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.35  tff(f_67, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.49/1.35  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.49/1.35  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.49/1.35  tff(c_44, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.49/1.35  tff(c_26, plain, (![A_12, B_13]: (r2_xboole_0(A_12, B_13) | B_13=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.35  tff(c_34, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.35  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.49/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.35  tff(c_232, plain, (![A_75, B_76, C_77, D_78]: (r2_hidden(k4_tarski(A_75, B_76), k2_zfmisc_1(C_77, D_78)) | ~r2_hidden(B_76, D_78) | ~r2_hidden(A_75, C_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.35  tff(c_50, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.49/1.35  tff(c_173, plain, (![A_59, C_60, B_61, D_62]: (r2_hidden(A_59, C_60) | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1(C_60, D_62)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.35  tff(c_176, plain, (![A_59, B_61]: (r2_hidden(A_59, '#skF_5') | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_173])).
% 2.49/1.35  tff(c_252, plain, (![A_75, B_76]: (r2_hidden(A_75, '#skF_5') | ~r2_hidden(B_76, '#skF_5') | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_232, c_176])).
% 2.49/1.35  tff(c_269, plain, (![B_81]: (~r2_hidden(B_81, '#skF_5'))), inference(splitLeft, [status(thm)], [c_252])).
% 2.49/1.35  tff(c_285, plain, (![B_82]: (r1_tarski('#skF_5', B_82))), inference(resolution, [status(thm)], [c_6, c_269])).
% 2.49/1.35  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.35  tff(c_106, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k4_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.35  tff(c_127, plain, (![D_46, A_47]: (~r2_hidden(D_46, k1_xboole_0) | ~r2_hidden(D_46, A_47))), inference(superposition, [status(thm), theory('equality')], [c_36, c_106])).
% 2.49/1.35  tff(c_148, plain, (![A_55, A_56]: (~r2_hidden('#skF_4'(A_55, k1_xboole_0), A_56) | ~r2_xboole_0(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_127])).
% 2.49/1.35  tff(c_154, plain, (![A_57]: (~r2_xboole_0(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_148])).
% 2.49/1.35  tff(c_159, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_154])).
% 2.49/1.35  tff(c_291, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_285, c_159])).
% 2.49/1.35  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_291])).
% 2.49/1.35  tff(c_298, plain, (![A_83]: (r2_hidden(A_83, '#skF_5') | ~r2_hidden(A_83, '#skF_6'))), inference(splitRight, [status(thm)], [c_252])).
% 2.49/1.35  tff(c_32, plain, (![A_14, B_15]: (~r2_hidden('#skF_4'(A_14, B_15), A_14) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.35  tff(c_344, plain, (![B_87]: (~r2_xboole_0('#skF_5', B_87) | ~r2_hidden('#skF_4'('#skF_5', B_87), '#skF_6'))), inference(resolution, [status(thm)], [c_298, c_32])).
% 2.49/1.35  tff(c_354, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_344])).
% 2.49/1.35  tff(c_357, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_354])).
% 2.49/1.35  tff(c_360, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_357])).
% 2.49/1.35  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.49/1.35  tff(c_144, plain, (![B_51, D_52, A_53, C_54]: (r2_hidden(B_51, D_52) | ~r2_hidden(k4_tarski(A_53, B_51), k2_zfmisc_1(C_54, D_52)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.49/1.35  tff(c_147, plain, (![B_51, A_53]: (r2_hidden(B_51, '#skF_6') | ~r2_hidden(k4_tarski(A_53, B_51), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_144])).
% 2.49/1.35  tff(c_253, plain, (![B_76, A_75]: (r2_hidden(B_76, '#skF_6') | ~r2_hidden(B_76, '#skF_5') | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_232, c_147])).
% 2.49/1.35  tff(c_424, plain, (![A_96]: (~r2_hidden(A_96, '#skF_6'))), inference(splitLeft, [status(thm)], [c_253])).
% 2.49/1.35  tff(c_448, plain, (![B_97]: (r1_tarski('#skF_6', B_97))), inference(resolution, [status(thm)], [c_6, c_424])).
% 2.49/1.35  tff(c_457, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_448, c_159])).
% 2.49/1.35  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_457])).
% 2.49/1.35  tff(c_510, plain, (![B_100]: (r2_hidden(B_100, '#skF_6') | ~r2_hidden(B_100, '#skF_5'))), inference(splitRight, [status(thm)], [c_253])).
% 2.49/1.35  tff(c_537, plain, (![B_101]: (r2_hidden('#skF_1'('#skF_5', B_101), '#skF_6') | r1_tarski('#skF_5', B_101))), inference(resolution, [status(thm)], [c_6, c_510])).
% 2.49/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.35  tff(c_547, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_537, c_4])).
% 2.49/1.35  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_360, c_547])).
% 2.49/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  Inference rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Ref     : 0
% 2.49/1.35  #Sup     : 98
% 2.49/1.35  #Fact    : 0
% 2.49/1.35  #Define  : 0
% 2.49/1.35  #Split   : 3
% 2.49/1.35  #Chain   : 0
% 2.49/1.35  #Close   : 0
% 2.49/1.35  
% 2.49/1.35  Ordering : KBO
% 2.49/1.35  
% 2.49/1.35  Simplification rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Subsume      : 17
% 2.49/1.35  #Demod        : 5
% 2.49/1.35  #Tautology    : 22
% 2.49/1.35  #SimpNegUnit  : 13
% 2.49/1.35  #BackRed      : 3
% 2.49/1.35  
% 2.49/1.35  #Partial instantiations: 0
% 2.49/1.35  #Strategies tried      : 1
% 2.49/1.35  
% 2.49/1.35  Timing (in seconds)
% 2.49/1.35  ----------------------
% 2.49/1.36  Preprocessing        : 0.30
% 2.49/1.36  Parsing              : 0.16
% 2.49/1.36  CNF conversion       : 0.02
% 2.49/1.36  Main loop            : 0.29
% 2.49/1.36  Inferencing          : 0.11
% 2.49/1.36  Reduction            : 0.07
% 2.49/1.36  Demodulation         : 0.05
% 2.49/1.36  BG Simplification    : 0.02
% 2.49/1.36  Subsumption          : 0.08
% 2.49/1.36  Abstraction          : 0.01
% 2.49/1.36  MUC search           : 0.00
% 2.49/1.36  Cooper               : 0.00
% 2.49/1.36  Total                : 0.62
% 2.49/1.36  Index Insertion      : 0.00
% 2.49/1.36  Index Deletion       : 0.00
% 2.49/1.36  Index Matching       : 0.00
% 2.49/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
