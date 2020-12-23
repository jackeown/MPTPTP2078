%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:09 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 121 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 196 expanded)
%              Number of equality atoms :   49 ( 162 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [B_12,C_13] : r1_tarski(k1_xboole_0,k2_tarski(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_30])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_88,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_107,plain,(
    ! [B_31,A_32] :
      ( k1_xboole_0 = B_31
      | k1_xboole_0 = A_32
      | k2_zfmisc_1(A_32,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_107])).

tff(c_119,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_110])).

tff(c_12,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_164,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_tarski(A_42,B_43) = k1_tarski(C_44)
      | ~ r1_tarski(k2_tarski(A_42,B_43),k1_tarski(C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [A_5,C_44] :
      ( k2_tarski(A_5,A_5) = k1_tarski(C_44)
      | ~ r1_tarski(k1_tarski(A_5),k1_tarski(C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_164])).

tff(c_173,plain,(
    ! [C_45,A_46] :
      ( k1_tarski(C_45) = k1_tarski(A_46)
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(C_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_170])).

tff(c_176,plain,(
    ! [C_45] :
      ( k1_tarski(C_45) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_xboole_0,k1_tarski(C_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_173])).

tff(c_184,plain,(
    ! [C_45] : k1_tarski(C_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_119,c_176])).

tff(c_148,plain,(
    ! [B_33,C_34,A_35] :
      ( r2_hidden(B_33,C_34)
      | k4_xboole_0(k2_tarski(A_35,B_33),C_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_151,plain,(
    ! [A_5,C_34] :
      ( r2_hidden(A_5,C_34)
      | k4_xboole_0(k1_tarski(A_5),C_34) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_190,plain,(
    ! [A_5,C_34] :
      ( r2_hidden(A_5,C_34)
      | k4_xboole_0(k1_xboole_0,C_34) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_151])).

tff(c_198,plain,(
    ! [A_5,C_34] : r2_hidden(A_5,C_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_190])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [B_56,A_57] : B_56 = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_198,c_2])).

tff(c_562,plain,(
    ! [B_56] : B_56 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_40])).

tff(c_574,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_562])).

tff(c_575,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_595,plain,(
    ! [B_240,A_241] :
      ( k1_xboole_0 = B_240
      | k1_xboole_0 = A_241
      | k2_zfmisc_1(A_241,B_240) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_598,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_595])).

tff(c_607,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_598])).

tff(c_576,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_612,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_576])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.22/1.28  
% 2.22/1.28  %Foreground sorts:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Background operators:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Foreground operators:
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.28  
% 2.22/1.29  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.22/1.29  tff(f_77, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.22/1.29  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.22/1.29  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.29  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 2.22/1.29  tff(f_46, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.22/1.29  tff(f_67, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.22/1.29  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.22/1.29  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.29  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.22/1.29  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.29  tff(c_71, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.29  tff(c_30, plain, (![B_12, C_13]: (r1_tarski(k1_xboole_0, k2_tarski(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.29  tff(c_76, plain, (![A_22]: (r1_tarski(k1_xboole_0, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_30])).
% 2.22/1.29  tff(c_38, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.22/1.29  tff(c_88, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.22/1.29  tff(c_107, plain, (![B_31, A_32]: (k1_xboole_0=B_31 | k1_xboole_0=A_32 | k2_zfmisc_1(A_32, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.29  tff(c_110, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88, c_107])).
% 2.22/1.29  tff(c_119, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_110])).
% 2.22/1.29  tff(c_12, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.29  tff(c_164, plain, (![A_42, B_43, C_44]: (k2_tarski(A_42, B_43)=k1_tarski(C_44) | ~r1_tarski(k2_tarski(A_42, B_43), k1_tarski(C_44)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.29  tff(c_170, plain, (![A_5, C_44]: (k2_tarski(A_5, A_5)=k1_tarski(C_44) | ~r1_tarski(k1_tarski(A_5), k1_tarski(C_44)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_164])).
% 2.22/1.29  tff(c_173, plain, (![C_45, A_46]: (k1_tarski(C_45)=k1_tarski(A_46) | ~r1_tarski(k1_tarski(A_46), k1_tarski(C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_170])).
% 2.22/1.29  tff(c_176, plain, (![C_45]: (k1_tarski(C_45)=k1_tarski('#skF_4') | ~r1_tarski(k1_xboole_0, k1_tarski(C_45)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_173])).
% 2.22/1.29  tff(c_184, plain, (![C_45]: (k1_tarski(C_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_119, c_176])).
% 2.22/1.29  tff(c_148, plain, (![B_33, C_34, A_35]: (r2_hidden(B_33, C_34) | k4_xboole_0(k2_tarski(A_35, B_33), C_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.29  tff(c_151, plain, (![A_5, C_34]: (r2_hidden(A_5, C_34) | k4_xboole_0(k1_tarski(A_5), C_34)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_148])).
% 2.22/1.29  tff(c_190, plain, (![A_5, C_34]: (r2_hidden(A_5, C_34) | k4_xboole_0(k1_xboole_0, C_34)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_151])).
% 2.22/1.29  tff(c_198, plain, (![A_5, C_34]: (r2_hidden(A_5, C_34))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_190])).
% 2.22/1.29  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.29  tff(c_254, plain, (![B_56, A_57]: (B_56=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_198, c_2])).
% 2.22/1.29  tff(c_562, plain, (![B_56]: (B_56!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_254, c_40])).
% 2.22/1.29  tff(c_574, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_562])).
% 2.22/1.29  tff(c_575, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.22/1.29  tff(c_595, plain, (![B_240, A_241]: (k1_xboole_0=B_240 | k1_xboole_0=A_241 | k2_zfmisc_1(A_241, B_240)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.29  tff(c_598, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_575, c_595])).
% 2.22/1.29  tff(c_607, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_598])).
% 2.22/1.29  tff(c_576, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.22/1.29  tff(c_612, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_607, c_576])).
% 2.22/1.29  tff(c_616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_612])).
% 2.22/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  Inference rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Ref     : 1
% 2.22/1.29  #Sup     : 122
% 2.22/1.29  #Fact    : 0
% 2.22/1.29  #Define  : 0
% 2.22/1.29  #Split   : 1
% 2.22/1.29  #Chain   : 0
% 2.22/1.29  #Close   : 0
% 2.22/1.29  
% 2.22/1.29  Ordering : KBO
% 2.22/1.29  
% 2.22/1.29  Simplification rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Subsume      : 11
% 2.22/1.29  #Demod        : 67
% 2.22/1.29  #Tautology    : 59
% 2.22/1.29  #SimpNegUnit  : 2
% 2.22/1.29  #BackRed      : 10
% 2.22/1.29  
% 2.22/1.29  #Partial instantiations: 126
% 2.22/1.29  #Strategies tried      : 1
% 2.22/1.29  
% 2.22/1.29  Timing (in seconds)
% 2.22/1.29  ----------------------
% 2.22/1.29  Preprocessing        : 0.29
% 2.22/1.29  Parsing              : 0.15
% 2.22/1.29  CNF conversion       : 0.02
% 2.22/1.29  Main loop            : 0.21
% 2.22/1.29  Inferencing          : 0.08
% 2.22/1.29  Reduction            : 0.07
% 2.22/1.29  Demodulation         : 0.05
% 2.22/1.29  BG Simplification    : 0.01
% 2.22/1.29  Subsumption          : 0.04
% 2.22/1.29  Abstraction          : 0.01
% 2.22/1.29  MUC search           : 0.00
% 2.22/1.29  Cooper               : 0.00
% 2.22/1.29  Total                : 0.53
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.30  Index Matching       : 0.00
% 2.22/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
