%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  89 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    ! [B_53,A_54] : k1_setfam_1(k2_tarski(B_53,A_54)) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_40,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_114,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_40])).

tff(c_172,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_267,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_86,B_87),B_88),B_87)
      | r1_tarski(k3_xboole_0(A_86,B_87),B_88) ) ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_301,plain,(
    ! [A_94,B_95] : r1_tarski(k3_xboole_0(A_94,B_95),B_95) ),
    inference(resolution,[status(thm)],[c_267,c_4])).

tff(c_312,plain,(
    ! [B_96,A_97] : r1_tarski(k3_xboole_0(B_96,A_97),B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_301])).

tff(c_42,plain,(
    ! [B_45,A_43] :
      ( B_45 = A_43
      | ~ r1_tarski(A_43,B_45)
      | ~ v1_zfmisc_1(B_45)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_477,plain,(
    ! [B_123,A_124] :
      ( k3_xboole_0(B_123,A_124) = B_123
      | ~ v1_zfmisc_1(B_123)
      | v1_xboole_0(B_123)
      | v1_xboole_0(k3_xboole_0(B_123,A_124)) ) ),
    inference(resolution,[status(thm)],[c_312,c_42])).

tff(c_46,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_480,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_477,c_46])).

tff(c_489,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_480])).

tff(c_490,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_489])).

tff(c_290,plain,(
    ! [A_86,B_87] : r1_tarski(k3_xboole_0(A_86,B_87),B_87) ),
    inference(resolution,[status(thm)],[c_267,c_4])).

tff(c_513,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_290])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.47/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.33  
% 2.47/1.34  tff(f_82, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.47/1.34  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.47/1.34  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.47/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.47/1.34  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.47/1.34  tff(f_70, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.47/1.34  tff(c_44, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.34  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.34  tff(c_48, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.34  tff(c_26, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.34  tff(c_93, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.34  tff(c_108, plain, (![B_53, A_54]: (k1_setfam_1(k2_tarski(B_53, A_54))=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_26, c_93])).
% 2.47/1.34  tff(c_40, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.34  tff(c_114, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_108, c_40])).
% 2.47/1.34  tff(c_172, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.34  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.34  tff(c_267, plain, (![A_86, B_87, B_88]: (r2_hidden('#skF_1'(k3_xboole_0(A_86, B_87), B_88), B_87) | r1_tarski(k3_xboole_0(A_86, B_87), B_88))), inference(resolution, [status(thm)], [c_172, c_10])).
% 2.47/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.34  tff(c_301, plain, (![A_94, B_95]: (r1_tarski(k3_xboole_0(A_94, B_95), B_95))), inference(resolution, [status(thm)], [c_267, c_4])).
% 2.47/1.34  tff(c_312, plain, (![B_96, A_97]: (r1_tarski(k3_xboole_0(B_96, A_97), B_96))), inference(superposition, [status(thm), theory('equality')], [c_114, c_301])).
% 2.47/1.34  tff(c_42, plain, (![B_45, A_43]: (B_45=A_43 | ~r1_tarski(A_43, B_45) | ~v1_zfmisc_1(B_45) | v1_xboole_0(B_45) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.47/1.34  tff(c_477, plain, (![B_123, A_124]: (k3_xboole_0(B_123, A_124)=B_123 | ~v1_zfmisc_1(B_123) | v1_xboole_0(B_123) | v1_xboole_0(k3_xboole_0(B_123, A_124)))), inference(resolution, [status(thm)], [c_312, c_42])).
% 2.47/1.34  tff(c_46, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.34  tff(c_480, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_477, c_46])).
% 2.47/1.34  tff(c_489, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_480])).
% 2.47/1.34  tff(c_490, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_489])).
% 2.47/1.34  tff(c_290, plain, (![A_86, B_87]: (r1_tarski(k3_xboole_0(A_86, B_87), B_87))), inference(resolution, [status(thm)], [c_267, c_4])).
% 2.47/1.34  tff(c_513, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_490, c_290])).
% 2.47/1.34  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_513])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 115
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 1
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 17
% 2.47/1.34  #Demod        : 22
% 2.47/1.34  #Tautology    : 46
% 2.47/1.34  #SimpNegUnit  : 4
% 2.47/1.34  #BackRed      : 1
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.31
% 2.47/1.34  Parsing              : 0.16
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.26
% 2.47/1.34  Inferencing          : 0.09
% 2.47/1.34  Reduction            : 0.08
% 2.47/1.34  Demodulation         : 0.06
% 2.47/1.34  BG Simplification    : 0.02
% 2.47/1.34  Subsumption          : 0.06
% 2.47/1.34  Abstraction          : 0.02
% 2.47/1.34  MUC search           : 0.00
% 2.47/1.34  Cooper               : 0.00
% 2.47/1.34  Total                : 0.60
% 2.47/1.34  Index Insertion      : 0.00
% 2.47/1.34  Index Deletion       : 0.00
% 2.47/1.34  Index Matching       : 0.00
% 2.47/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
