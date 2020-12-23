%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 114 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_7 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_setfam_1(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_26,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_setfam_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_53] : r1_setfam_1(A_53,A_53) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_272,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_1'(A_127,B_128,C_129),B_128)
      | r2_hidden('#skF_1'(A_127,B_128,C_129),A_127)
      | r2_hidden('#skF_2'(A_127,B_128,C_129),C_129)
      | k2_xboole_0(A_127,B_128) = C_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_398,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_1'(A_144,B_145,A_144),B_145)
      | r2_hidden('#skF_2'(A_144,B_145,A_144),A_144)
      | k2_xboole_0(A_144,B_145) = A_144 ) ),
    inference(resolution,[status(thm)],[c_272,c_16])).

tff(c_417,plain,(
    ! [B_145] :
      ( r2_hidden('#skF_2'(B_145,B_145,B_145),B_145)
      | k2_xboole_0(B_145,B_145) = B_145 ) ),
    inference(resolution,[status(thm)],[c_398,c_16])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_527,plain,(
    ! [B_154,C_155] :
      ( ~ r2_hidden('#skF_2'(B_154,B_154,C_155),B_154)
      | k2_xboole_0(B_154,B_154) = C_155
      | r2_hidden('#skF_1'(B_154,B_154,C_155),B_154) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_546,plain,(
    ! [B_156] :
      ( ~ r2_hidden('#skF_2'(B_156,B_156,B_156),B_156)
      | k2_xboole_0(B_156,B_156) = B_156 ) ),
    inference(resolution,[status(thm)],[c_527,c_12])).

tff(c_573,plain,(
    ! [B_157] : k2_xboole_0(B_157,B_157) = B_157 ),
    inference(resolution,[status(thm)],[c_417,c_546])).

tff(c_28,plain,(
    ! [E_51,F_52,A_19,B_20] :
      ( r2_hidden(k2_xboole_0(E_51,F_52),k2_setfam_1(A_19,B_20))
      | ~ r2_hidden(F_52,B_20)
      | ~ r2_hidden(E_51,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_669,plain,(
    ! [B_163,A_164,B_165] :
      ( r2_hidden(B_163,k2_setfam_1(A_164,B_165))
      | ~ r2_hidden(B_163,B_165)
      | ~ r2_hidden(B_163,A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_28])).

tff(c_22,plain,(
    ! [A_7,B_8,C_17] :
      ( r2_hidden('#skF_4'(A_7,B_8,C_17),B_8)
      | ~ r2_hidden(C_17,A_7)
      | ~ r1_setfam_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [C_70,A_71,B_72] :
      ( r1_tarski(C_70,'#skF_4'(A_71,B_72,C_70))
      | ~ r2_hidden(C_70,A_71)
      | ~ r1_setfam_1(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_7,B_8,D_16] :
      ( ~ r1_tarski('#skF_3'(A_7,B_8),D_16)
      | ~ r2_hidden(D_16,B_8)
      | r1_setfam_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [A_104,B_105,A_106,B_107] :
      ( ~ r2_hidden('#skF_4'(A_104,B_105,'#skF_3'(A_106,B_107)),B_107)
      | r1_setfam_1(A_106,B_107)
      | ~ r2_hidden('#skF_3'(A_106,B_107),A_104)
      | ~ r1_setfam_1(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_74,c_24])).

tff(c_174,plain,(
    ! [A_106,B_8,A_7] :
      ( r1_setfam_1(A_106,B_8)
      | ~ r2_hidden('#skF_3'(A_106,B_8),A_7)
      | ~ r1_setfam_1(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_161])).

tff(c_1413,plain,(
    ! [A_254,B_255,A_256,B_257] :
      ( r1_setfam_1(A_254,B_255)
      | ~ r1_setfam_1(k2_setfam_1(A_256,B_257),B_255)
      | ~ r2_hidden('#skF_3'(A_254,B_255),B_257)
      | ~ r2_hidden('#skF_3'(A_254,B_255),A_256) ) ),
    inference(resolution,[status(thm)],[c_669,c_174])).

tff(c_2649,plain,(
    ! [A_343,A_344,B_345] :
      ( r1_setfam_1(A_343,k2_setfam_1(A_344,B_345))
      | ~ r2_hidden('#skF_3'(A_343,k2_setfam_1(A_344,B_345)),B_345)
      | ~ r2_hidden('#skF_3'(A_343,k2_setfam_1(A_344,B_345)),A_344) ) ),
    inference(resolution,[status(thm)],[c_52,c_1413])).

tff(c_2694,plain,(
    ! [A_346,A_347] :
      ( ~ r2_hidden('#skF_3'(A_346,k2_setfam_1(A_347,A_346)),A_347)
      | r1_setfam_1(A_346,k2_setfam_1(A_347,A_346)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2649])).

tff(c_2739,plain,(
    ! [A_7] : r1_setfam_1(A_7,k2_setfam_1(A_7,A_7)) ),
    inference(resolution,[status(thm)],[c_26,c_2694])).

tff(c_54,plain,(
    ~ r1_setfam_1('#skF_11',k2_setfam_1('#skF_11','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:48:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.92  
% 4.92/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.92  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_1 > #skF_11 > #skF_6 > #skF_10 > #skF_9 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_7 > #skF_8
% 4.92/1.92  
% 4.92/1.92  %Foreground sorts:
% 4.92/1.92  
% 4.92/1.92  
% 4.92/1.92  %Background operators:
% 4.92/1.92  
% 4.92/1.92  
% 4.92/1.92  %Foreground operators:
% 4.92/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.92  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 4.92/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.92  tff('#skF_11', type, '#skF_11': $i).
% 4.92/1.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.92/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.92  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.92  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.92/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.92/1.92  
% 4.92/1.94  tff(f_46, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 4.92/1.94  tff(f_60, axiom, (![A, B]: r1_setfam_1(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_setfam_1)).
% 4.92/1.94  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.92/1.94  tff(f_58, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 4.92/1.94  tff(f_63, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 4.92/1.94  tff(c_26, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_setfam_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.92/1.94  tff(c_52, plain, (![A_53]: (r1_setfam_1(A_53, A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.92/1.94  tff(c_272, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_1'(A_127, B_128, C_129), B_128) | r2_hidden('#skF_1'(A_127, B_128, C_129), A_127) | r2_hidden('#skF_2'(A_127, B_128, C_129), C_129) | k2_xboole_0(A_127, B_128)=C_129)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.94  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.94  tff(c_398, plain, (![A_144, B_145]: (r2_hidden('#skF_1'(A_144, B_145, A_144), B_145) | r2_hidden('#skF_2'(A_144, B_145, A_144), A_144) | k2_xboole_0(A_144, B_145)=A_144)), inference(resolution, [status(thm)], [c_272, c_16])).
% 4.92/1.94  tff(c_417, plain, (![B_145]: (r2_hidden('#skF_2'(B_145, B_145, B_145), B_145) | k2_xboole_0(B_145, B_145)=B_145)), inference(resolution, [status(thm)], [c_398, c_16])).
% 4.92/1.94  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.94  tff(c_527, plain, (![B_154, C_155]: (~r2_hidden('#skF_2'(B_154, B_154, C_155), B_154) | k2_xboole_0(B_154, B_154)=C_155 | r2_hidden('#skF_1'(B_154, B_154, C_155), B_154))), inference(factorization, [status(thm), theory('equality')], [c_10])).
% 4.92/1.94  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.94  tff(c_546, plain, (![B_156]: (~r2_hidden('#skF_2'(B_156, B_156, B_156), B_156) | k2_xboole_0(B_156, B_156)=B_156)), inference(resolution, [status(thm)], [c_527, c_12])).
% 4.92/1.94  tff(c_573, plain, (![B_157]: (k2_xboole_0(B_157, B_157)=B_157)), inference(resolution, [status(thm)], [c_417, c_546])).
% 4.92/1.94  tff(c_28, plain, (![E_51, F_52, A_19, B_20]: (r2_hidden(k2_xboole_0(E_51, F_52), k2_setfam_1(A_19, B_20)) | ~r2_hidden(F_52, B_20) | ~r2_hidden(E_51, A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.92/1.94  tff(c_669, plain, (![B_163, A_164, B_165]: (r2_hidden(B_163, k2_setfam_1(A_164, B_165)) | ~r2_hidden(B_163, B_165) | ~r2_hidden(B_163, A_164))), inference(superposition, [status(thm), theory('equality')], [c_573, c_28])).
% 4.92/1.94  tff(c_22, plain, (![A_7, B_8, C_17]: (r2_hidden('#skF_4'(A_7, B_8, C_17), B_8) | ~r2_hidden(C_17, A_7) | ~r1_setfam_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.92/1.94  tff(c_74, plain, (![C_70, A_71, B_72]: (r1_tarski(C_70, '#skF_4'(A_71, B_72, C_70)) | ~r2_hidden(C_70, A_71) | ~r1_setfam_1(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.92/1.94  tff(c_24, plain, (![A_7, B_8, D_16]: (~r1_tarski('#skF_3'(A_7, B_8), D_16) | ~r2_hidden(D_16, B_8) | r1_setfam_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.92/1.94  tff(c_161, plain, (![A_104, B_105, A_106, B_107]: (~r2_hidden('#skF_4'(A_104, B_105, '#skF_3'(A_106, B_107)), B_107) | r1_setfam_1(A_106, B_107) | ~r2_hidden('#skF_3'(A_106, B_107), A_104) | ~r1_setfam_1(A_104, B_105))), inference(resolution, [status(thm)], [c_74, c_24])).
% 4.92/1.94  tff(c_174, plain, (![A_106, B_8, A_7]: (r1_setfam_1(A_106, B_8) | ~r2_hidden('#skF_3'(A_106, B_8), A_7) | ~r1_setfam_1(A_7, B_8))), inference(resolution, [status(thm)], [c_22, c_161])).
% 4.92/1.94  tff(c_1413, plain, (![A_254, B_255, A_256, B_257]: (r1_setfam_1(A_254, B_255) | ~r1_setfam_1(k2_setfam_1(A_256, B_257), B_255) | ~r2_hidden('#skF_3'(A_254, B_255), B_257) | ~r2_hidden('#skF_3'(A_254, B_255), A_256))), inference(resolution, [status(thm)], [c_669, c_174])).
% 4.92/1.94  tff(c_2649, plain, (![A_343, A_344, B_345]: (r1_setfam_1(A_343, k2_setfam_1(A_344, B_345)) | ~r2_hidden('#skF_3'(A_343, k2_setfam_1(A_344, B_345)), B_345) | ~r2_hidden('#skF_3'(A_343, k2_setfam_1(A_344, B_345)), A_344))), inference(resolution, [status(thm)], [c_52, c_1413])).
% 4.92/1.94  tff(c_2694, plain, (![A_346, A_347]: (~r2_hidden('#skF_3'(A_346, k2_setfam_1(A_347, A_346)), A_347) | r1_setfam_1(A_346, k2_setfam_1(A_347, A_346)))), inference(resolution, [status(thm)], [c_26, c_2649])).
% 4.92/1.94  tff(c_2739, plain, (![A_7]: (r1_setfam_1(A_7, k2_setfam_1(A_7, A_7)))), inference(resolution, [status(thm)], [c_26, c_2694])).
% 4.92/1.94  tff(c_54, plain, (~r1_setfam_1('#skF_11', k2_setfam_1('#skF_11', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.92/1.94  tff(c_2742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2739, c_54])).
% 4.92/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  
% 4.92/1.94  Inference rules
% 4.92/1.94  ----------------------
% 4.92/1.94  #Ref     : 0
% 4.92/1.94  #Sup     : 610
% 4.92/1.94  #Fact    : 8
% 4.92/1.94  #Define  : 0
% 4.92/1.94  #Split   : 0
% 4.92/1.94  #Chain   : 0
% 4.92/1.94  #Close   : 0
% 4.92/1.94  
% 4.92/1.94  Ordering : KBO
% 4.92/1.94  
% 4.92/1.94  Simplification rules
% 4.92/1.94  ----------------------
% 4.92/1.94  #Subsume      : 93
% 4.92/1.94  #Demod        : 165
% 4.92/1.94  #Tautology    : 101
% 4.92/1.94  #SimpNegUnit  : 0
% 4.92/1.94  #BackRed      : 3
% 4.92/1.94  
% 4.92/1.94  #Partial instantiations: 0
% 4.92/1.94  #Strategies tried      : 1
% 4.92/1.94  
% 4.92/1.94  Timing (in seconds)
% 4.92/1.94  ----------------------
% 4.92/1.94  Preprocessing        : 0.30
% 4.92/1.94  Parsing              : 0.15
% 4.92/1.94  CNF conversion       : 0.03
% 4.92/1.94  Main loop            : 0.89
% 4.92/1.94  Inferencing          : 0.31
% 4.92/1.94  Reduction            : 0.22
% 4.92/1.94  Demodulation         : 0.16
% 4.92/1.94  BG Simplification    : 0.04
% 4.92/1.94  Subsumption          : 0.26
% 4.92/1.94  Abstraction          : 0.04
% 4.92/1.94  MUC search           : 0.00
% 4.92/1.94  Cooper               : 0.00
% 4.92/1.94  Total                : 1.21
% 4.92/1.94  Index Insertion      : 0.00
% 4.92/1.94  Index Deletion       : 0.00
% 4.92/1.94  Index Matching       : 0.00
% 4.92/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
