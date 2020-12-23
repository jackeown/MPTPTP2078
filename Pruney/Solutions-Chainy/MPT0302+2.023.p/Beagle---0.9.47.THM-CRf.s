%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 156 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 325 expanded)
%              Number of equality atoms :   15 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
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

tff(c_54,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_410,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( r2_hidden(k4_tarski(A_128,B_129),k2_zfmisc_1(C_130,D_131))
      | ~ r2_hidden(B_129,D_131)
      | ~ r2_hidden(A_128,C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_118,plain,(
    ! [B_67,D_68,A_69,C_70] :
      ( r2_hidden(B_67,D_68)
      | ~ r2_hidden(k4_tarski(A_69,B_67),k2_zfmisc_1(C_70,D_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_121,plain,(
    ! [B_67,A_69] :
      ( r2_hidden(B_67,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_69,B_67),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_118])).

tff(c_432,plain,(
    ! [B_129,A_128] :
      ( r2_hidden(B_129,'#skF_8')
      | ~ r2_hidden(B_129,'#skF_9')
      | ~ r2_hidden(A_128,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_410,c_121])).

tff(c_440,plain,(
    ! [A_132] : ~ r2_hidden(A_132,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_585,plain,(
    ! [B_139] : r1_tarski('#skF_8',B_139) ),
    inference(resolution,[status(thm)],[c_6,c_440])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,B_65)
      | ~ r2_hidden(C_66,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,(
    ! [C_71,A_72] :
      ( ~ r2_hidden(C_71,k1_xboole_0)
      | ~ r2_hidden(C_71,A_72) ) ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_158,plain,(
    ! [A_76,A_77] :
      ( ~ r2_hidden('#skF_3'(A_76,k1_xboole_0),A_77)
      | ~ r2_xboole_0(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_168,plain,(
    ! [A_82] : ~ r2_xboole_0(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_158])).

tff(c_173,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_594,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_585,c_173])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_594])).

tff(c_602,plain,(
    ! [B_140] :
      ( r2_hidden(B_140,'#skF_8')
      | ~ r2_hidden(B_140,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_695,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_1'('#skF_9',B_144),'#skF_8')
      | r1_tarski('#skF_9',B_144) ) ),
    inference(resolution,[status(thm)],[c_6,c_602])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_706,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_695,c_4])).

tff(c_101,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_279,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden('#skF_3'(A_101,B_102),B_103)
      | ~ r1_tarski(B_102,B_103)
      | ~ r2_xboole_0(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),A_13)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_313,plain,(
    ! [B_106,B_107] :
      ( ~ r1_tarski(B_106,B_107)
      | ~ r2_xboole_0(B_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_279,c_20])).

tff(c_317,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_313])).

tff(c_708,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_706,c_317])).

tff(c_711,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_708])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_665,plain,(
    ! [A_141,B_142] :
      ( r2_hidden(k4_tarski(A_141,B_142),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_142,'#skF_8')
      | ~ r2_hidden(A_141,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_410])).

tff(c_48,plain,(
    ! [B_38,D_40,A_37,C_39] :
      ( r2_hidden(B_38,D_40)
      | ~ r2_hidden(k4_tarski(A_37,B_38),k2_zfmisc_1(C_39,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_686,plain,(
    ! [B_142,A_141] :
      ( r2_hidden(B_142,'#skF_9')
      | ~ r2_hidden(B_142,'#skF_8')
      | ~ r2_hidden(A_141,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_665,c_48])).

tff(c_746,plain,(
    ! [A_149] : ~ r2_hidden(A_149,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_686])).

tff(c_899,plain,(
    ! [B_157] : r1_tarski('#skF_9',B_157) ),
    inference(resolution,[status(thm)],[c_6,c_746])).

tff(c_908,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_899,c_173])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_908])).

tff(c_916,plain,(
    ! [B_158] :
      ( r2_hidden(B_158,'#skF_9')
      | ~ r2_hidden(B_158,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_942,plain,(
    ! [A_159] :
      ( r1_tarski(A_159,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_159,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_916,c_4])).

tff(c_954,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_942])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_711,c_711,c_954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.49  
% 2.92/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.49  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.99/1.49  
% 2.99/1.49  %Foreground sorts:
% 2.99/1.49  
% 2.99/1.49  
% 2.99/1.49  %Background operators:
% 2.99/1.49  
% 2.99/1.49  
% 2.99/1.49  %Foreground operators:
% 2.99/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.99/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.49  tff('#skF_9', type, '#skF_9': $i).
% 2.99/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.99/1.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.99/1.49  tff('#skF_8', type, '#skF_8': $i).
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.99/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.99/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.99/1.49  
% 2.99/1.50  tff(f_97, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.99/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.99/1.50  tff(f_87, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.99/1.50  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.99/1.50  tff(f_67, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.99/1.50  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.99/1.50  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.99/1.50  tff(c_54, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.50  tff(c_58, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.50  tff(c_410, plain, (![A_128, B_129, C_130, D_131]: (r2_hidden(k4_tarski(A_128, B_129), k2_zfmisc_1(C_130, D_131)) | ~r2_hidden(B_129, D_131) | ~r2_hidden(A_128, C_130))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.50  tff(c_60, plain, (k2_zfmisc_1('#skF_9', '#skF_8')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.50  tff(c_118, plain, (![B_67, D_68, A_69, C_70]: (r2_hidden(B_67, D_68) | ~r2_hidden(k4_tarski(A_69, B_67), k2_zfmisc_1(C_70, D_68)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.50  tff(c_121, plain, (![B_67, A_69]: (r2_hidden(B_67, '#skF_8') | ~r2_hidden(k4_tarski(A_69, B_67), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_118])).
% 2.99/1.50  tff(c_432, plain, (![B_129, A_128]: (r2_hidden(B_129, '#skF_8') | ~r2_hidden(B_129, '#skF_9') | ~r2_hidden(A_128, '#skF_8'))), inference(resolution, [status(thm)], [c_410, c_121])).
% 2.99/1.50  tff(c_440, plain, (![A_132]: (~r2_hidden(A_132, '#skF_8'))), inference(splitLeft, [status(thm)], [c_432])).
% 2.99/1.50  tff(c_585, plain, (![B_139]: (r1_tarski('#skF_8', B_139))), inference(resolution, [status(thm)], [c_6, c_440])).
% 2.99/1.50  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.50  tff(c_22, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.50  tff(c_26, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.50  tff(c_114, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, B_65) | ~r2_hidden(C_66, A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.50  tff(c_122, plain, (![C_71, A_72]: (~r2_hidden(C_71, k1_xboole_0) | ~r2_hidden(C_71, A_72))), inference(resolution, [status(thm)], [c_26, c_114])).
% 2.99/1.50  tff(c_158, plain, (![A_76, A_77]: (~r2_hidden('#skF_3'(A_76, k1_xboole_0), A_77) | ~r2_xboole_0(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_122])).
% 2.99/1.50  tff(c_168, plain, (![A_82]: (~r2_xboole_0(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_158])).
% 2.99/1.50  tff(c_173, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_168])).
% 2.99/1.50  tff(c_594, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_585, c_173])).
% 2.99/1.50  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_594])).
% 2.99/1.50  tff(c_602, plain, (![B_140]: (r2_hidden(B_140, '#skF_8') | ~r2_hidden(B_140, '#skF_9'))), inference(splitRight, [status(thm)], [c_432])).
% 2.99/1.50  tff(c_695, plain, (![B_144]: (r2_hidden('#skF_1'('#skF_9', B_144), '#skF_8') | r1_tarski('#skF_9', B_144))), inference(resolution, [status(thm)], [c_6, c_602])).
% 2.99/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.50  tff(c_706, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_695, c_4])).
% 2.99/1.50  tff(c_101, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.50  tff(c_279, plain, (![A_101, B_102, B_103]: (r2_hidden('#skF_3'(A_101, B_102), B_103) | ~r1_tarski(B_102, B_103) | ~r2_xboole_0(A_101, B_102))), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.99/1.50  tff(c_20, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), A_13) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.50  tff(c_313, plain, (![B_106, B_107]: (~r1_tarski(B_106, B_107) | ~r2_xboole_0(B_107, B_106))), inference(resolution, [status(thm)], [c_279, c_20])).
% 2.99/1.50  tff(c_317, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_313])).
% 2.99/1.50  tff(c_708, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_706, c_317])).
% 2.99/1.50  tff(c_711, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_54, c_708])).
% 2.99/1.50  tff(c_56, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.50  tff(c_665, plain, (![A_141, B_142]: (r2_hidden(k4_tarski(A_141, B_142), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_142, '#skF_8') | ~r2_hidden(A_141, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_410])).
% 2.99/1.50  tff(c_48, plain, (![B_38, D_40, A_37, C_39]: (r2_hidden(B_38, D_40) | ~r2_hidden(k4_tarski(A_37, B_38), k2_zfmisc_1(C_39, D_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.50  tff(c_686, plain, (![B_142, A_141]: (r2_hidden(B_142, '#skF_9') | ~r2_hidden(B_142, '#skF_8') | ~r2_hidden(A_141, '#skF_9'))), inference(resolution, [status(thm)], [c_665, c_48])).
% 2.99/1.50  tff(c_746, plain, (![A_149]: (~r2_hidden(A_149, '#skF_9'))), inference(splitLeft, [status(thm)], [c_686])).
% 2.99/1.50  tff(c_899, plain, (![B_157]: (r1_tarski('#skF_9', B_157))), inference(resolution, [status(thm)], [c_6, c_746])).
% 2.99/1.50  tff(c_908, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_899, c_173])).
% 2.99/1.50  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_908])).
% 2.99/1.50  tff(c_916, plain, (![B_158]: (r2_hidden(B_158, '#skF_9') | ~r2_hidden(B_158, '#skF_8'))), inference(splitRight, [status(thm)], [c_686])).
% 2.99/1.50  tff(c_942, plain, (![A_159]: (r1_tarski(A_159, '#skF_9') | ~r2_hidden('#skF_1'(A_159, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_916, c_4])).
% 2.99/1.50  tff(c_954, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_6, c_942])).
% 2.99/1.50  tff(c_961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_711, c_711, c_954])).
% 2.99/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  Inference rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Ref     : 0
% 2.99/1.50  #Sup     : 192
% 2.99/1.50  #Fact    : 0
% 2.99/1.50  #Define  : 0
% 2.99/1.50  #Split   : 3
% 2.99/1.50  #Chain   : 0
% 2.99/1.50  #Close   : 0
% 2.99/1.50  
% 2.99/1.50  Ordering : KBO
% 2.99/1.50  
% 2.99/1.50  Simplification rules
% 2.99/1.50  ----------------------
% 2.99/1.50  #Subsume      : 49
% 2.99/1.50  #Demod        : 24
% 2.99/1.50  #Tautology    : 30
% 2.99/1.50  #SimpNegUnit  : 7
% 2.99/1.50  #BackRed      : 2
% 2.99/1.50  
% 2.99/1.50  #Partial instantiations: 0
% 2.99/1.50  #Strategies tried      : 1
% 2.99/1.50  
% 2.99/1.50  Timing (in seconds)
% 2.99/1.50  ----------------------
% 2.99/1.51  Preprocessing        : 0.33
% 2.99/1.51  Parsing              : 0.17
% 2.99/1.51  CNF conversion       : 0.03
% 2.99/1.51  Main loop            : 0.37
% 2.99/1.51  Inferencing          : 0.14
% 2.99/1.51  Reduction            : 0.09
% 2.99/1.51  Demodulation         : 0.06
% 2.99/1.51  BG Simplification    : 0.02
% 2.99/1.51  Subsumption          : 0.08
% 2.99/1.51  Abstraction          : 0.02
% 2.99/1.51  MUC search           : 0.00
% 2.99/1.51  Cooper               : 0.00
% 2.99/1.51  Total                : 0.73
% 2.99/1.51  Index Insertion      : 0.00
% 2.99/1.51  Index Deletion       : 0.00
% 2.99/1.51  Index Matching       : 0.00
% 2.99/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
