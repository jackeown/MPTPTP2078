%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 166 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_59,B_60,B_61] :
      ( r2_hidden('#skF_2'(A_59,B_60),B_61)
      | ~ r1_tarski(B_60,B_61)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_228,plain,(
    ! [A_76,B_77,B_78,B_79] :
      ( r2_hidden('#skF_2'(A_76,B_77),B_78)
      | ~ r1_tarski(B_79,B_78)
      | ~ r1_tarski(B_77,B_79)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_251,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),'#skF_4')
      | ~ r1_tarski(B_84,'#skF_3')
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( v3_ordinal1(A_16)
      | ~ r2_hidden(A_16,B_17)
      | ~ v3_ordinal1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_256,plain,(
    ! [A_83,B_84] :
      ( v3_ordinal1('#skF_2'(A_83,B_84))
      | ~ v3_ordinal1('#skF_4')
      | ~ r1_tarski(B_84,'#skF_3')
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_251,c_20])).

tff(c_260,plain,(
    ! [A_83,B_84] :
      ( v3_ordinal1('#skF_2'(A_83,B_84))
      | ~ r1_tarski(B_84,'#skF_3')
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_256])).

tff(c_34,plain,(
    ! [C_24] :
      ( v3_ordinal1('#skF_5'(C_24))
      | ~ r2_hidden(C_24,'#skF_3')
      | ~ v3_ordinal1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ! [C_24] :
      ( r2_hidden('#skF_5'(C_24),'#skF_3')
      | ~ r2_hidden(C_24,'#skF_3')
      | ~ v3_ordinal1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [B_20,A_18] :
      ( r2_hidden(B_20,A_18)
      | r1_ordinal1(A_18,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,'#skF_2'(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_542,plain,(
    ! [B_134,B_135,A_136] :
      ( ~ r2_hidden(B_134,B_135)
      | ~ r2_hidden(A_136,B_135)
      | r1_ordinal1('#skF_2'(A_136,B_135),B_134)
      | ~ v3_ordinal1(B_134)
      | ~ v3_ordinal1('#skF_2'(A_136,B_135)) ) ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_30,plain,(
    ! [C_24] :
      ( ~ r1_ordinal1(C_24,'#skF_5'(C_24))
      | ~ r2_hidden(C_24,'#skF_3')
      | ~ v3_ordinal1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_594,plain,(
    ! [A_139,B_140] :
      ( ~ r2_hidden('#skF_2'(A_139,B_140),'#skF_3')
      | ~ r2_hidden('#skF_5'('#skF_2'(A_139,B_140)),B_140)
      | ~ r2_hidden(A_139,B_140)
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_139,B_140)))
      | ~ v3_ordinal1('#skF_2'(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_542,c_30])).

tff(c_695,plain,(
    ! [A_155] :
      ( ~ r2_hidden(A_155,'#skF_3')
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_155,'#skF_3')))
      | ~ r2_hidden('#skF_2'(A_155,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_155,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_594])).

tff(c_869,plain,(
    ! [A_165] :
      ( ~ r2_hidden(A_165,'#skF_3')
      | ~ r2_hidden('#skF_2'(A_165,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_165,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_695])).

tff(c_893,plain,(
    ! [A_166] :
      ( ~ v3_ordinal1('#skF_2'(A_166,'#skF_3'))
      | ~ r2_hidden(A_166,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_869])).

tff(c_897,plain,(
    ! [A_83] :
      ( ~ r1_tarski('#skF_3','#skF_3')
      | ~ r2_hidden(A_83,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_260,c_893])).

tff(c_911,plain,(
    ! [A_167] : ~ r2_hidden(A_167,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_897])).

tff(c_949,plain,(
    ! [B_168] : r1_tarski('#skF_3',B_168) ),
    inference(resolution,[status(thm)],[c_6,c_911])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_57])).

tff(c_982,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_949,c_68])).

tff(c_1002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.47  
% 3.20/1.48  tff(f_90, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 3.20/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.48  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.48  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.20/1.48  tff(f_59, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.20/1.48  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.20/1.48  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.48  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.48  tff(c_28, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_18, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.48  tff(c_84, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_162, plain, (![A_59, B_60, B_61]: (r2_hidden('#skF_2'(A_59, B_60), B_61) | ~r1_tarski(B_60, B_61) | ~r2_hidden(A_59, B_60))), inference(resolution, [status(thm)], [c_18, c_84])).
% 3.20/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.48  tff(c_228, plain, (![A_76, B_77, B_78, B_79]: (r2_hidden('#skF_2'(A_76, B_77), B_78) | ~r1_tarski(B_79, B_78) | ~r1_tarski(B_77, B_79) | ~r2_hidden(A_76, B_77))), inference(resolution, [status(thm)], [c_162, c_2])).
% 3.20/1.48  tff(c_251, plain, (![A_83, B_84]: (r2_hidden('#skF_2'(A_83, B_84), '#skF_4') | ~r1_tarski(B_84, '#skF_3') | ~r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_26, c_228])).
% 3.20/1.48  tff(c_20, plain, (![A_16, B_17]: (v3_ordinal1(A_16) | ~r2_hidden(A_16, B_17) | ~v3_ordinal1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.48  tff(c_256, plain, (![A_83, B_84]: (v3_ordinal1('#skF_2'(A_83, B_84)) | ~v3_ordinal1('#skF_4') | ~r1_tarski(B_84, '#skF_3') | ~r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_251, c_20])).
% 3.20/1.48  tff(c_260, plain, (![A_83, B_84]: (v3_ordinal1('#skF_2'(A_83, B_84)) | ~r1_tarski(B_84, '#skF_3') | ~r2_hidden(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_256])).
% 3.20/1.48  tff(c_34, plain, (![C_24]: (v3_ordinal1('#skF_5'(C_24)) | ~r2_hidden(C_24, '#skF_3') | ~v3_ordinal1(C_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_32, plain, (![C_24]: (r2_hidden('#skF_5'(C_24), '#skF_3') | ~r2_hidden(C_24, '#skF_3') | ~v3_ordinal1(C_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_22, plain, (![B_20, A_18]: (r2_hidden(B_20, A_18) | r1_ordinal1(A_18, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.48  tff(c_123, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, '#skF_2'(A_54, B_55)) | ~r2_hidden(D_53, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.48  tff(c_542, plain, (![B_134, B_135, A_136]: (~r2_hidden(B_134, B_135) | ~r2_hidden(A_136, B_135) | r1_ordinal1('#skF_2'(A_136, B_135), B_134) | ~v3_ordinal1(B_134) | ~v3_ordinal1('#skF_2'(A_136, B_135)))), inference(resolution, [status(thm)], [c_22, c_123])).
% 3.20/1.48  tff(c_30, plain, (![C_24]: (~r1_ordinal1(C_24, '#skF_5'(C_24)) | ~r2_hidden(C_24, '#skF_3') | ~v3_ordinal1(C_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.48  tff(c_594, plain, (![A_139, B_140]: (~r2_hidden('#skF_2'(A_139, B_140), '#skF_3') | ~r2_hidden('#skF_5'('#skF_2'(A_139, B_140)), B_140) | ~r2_hidden(A_139, B_140) | ~v3_ordinal1('#skF_5'('#skF_2'(A_139, B_140))) | ~v3_ordinal1('#skF_2'(A_139, B_140)))), inference(resolution, [status(thm)], [c_542, c_30])).
% 3.20/1.48  tff(c_695, plain, (![A_155]: (~r2_hidden(A_155, '#skF_3') | ~v3_ordinal1('#skF_5'('#skF_2'(A_155, '#skF_3'))) | ~r2_hidden('#skF_2'(A_155, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_155, '#skF_3')))), inference(resolution, [status(thm)], [c_32, c_594])).
% 3.20/1.48  tff(c_869, plain, (![A_165]: (~r2_hidden(A_165, '#skF_3') | ~r2_hidden('#skF_2'(A_165, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_165, '#skF_3')))), inference(resolution, [status(thm)], [c_34, c_695])).
% 3.20/1.48  tff(c_893, plain, (![A_166]: (~v3_ordinal1('#skF_2'(A_166, '#skF_3')) | ~r2_hidden(A_166, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_869])).
% 3.20/1.48  tff(c_897, plain, (![A_83]: (~r1_tarski('#skF_3', '#skF_3') | ~r2_hidden(A_83, '#skF_3'))), inference(resolution, [status(thm)], [c_260, c_893])).
% 3.20/1.48  tff(c_911, plain, (![A_167]: (~r2_hidden(A_167, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_897])).
% 3.20/1.48  tff(c_949, plain, (![B_168]: (r1_tarski('#skF_3', B_168))), inference(resolution, [status(thm)], [c_6, c_911])).
% 3.20/1.48  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.48  tff(c_57, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.48  tff(c_68, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_57])).
% 3.20/1.48  tff(c_982, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_949, c_68])).
% 3.20/1.48  tff(c_1002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_982])).
% 3.20/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  Inference rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Ref     : 0
% 3.20/1.48  #Sup     : 198
% 3.20/1.48  #Fact    : 0
% 3.20/1.48  #Define  : 0
% 3.20/1.48  #Split   : 8
% 3.20/1.48  #Chain   : 0
% 3.20/1.48  #Close   : 0
% 3.20/1.48  
% 3.20/1.48  Ordering : KBO
% 3.20/1.48  
% 3.20/1.48  Simplification rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Subsume      : 117
% 3.20/1.48  #Demod        : 28
% 3.20/1.48  #Tautology    : 22
% 3.20/1.48  #SimpNegUnit  : 23
% 3.20/1.48  #BackRed      : 8
% 3.20/1.48  
% 3.20/1.48  #Partial instantiations: 0
% 3.20/1.48  #Strategies tried      : 1
% 3.20/1.48  
% 3.20/1.48  Timing (in seconds)
% 3.20/1.48  ----------------------
% 3.20/1.48  Preprocessing        : 0.29
% 3.20/1.48  Parsing              : 0.16
% 3.20/1.48  CNF conversion       : 0.02
% 3.20/1.48  Main loop            : 0.42
% 3.20/1.48  Inferencing          : 0.16
% 3.20/1.48  Reduction            : 0.10
% 3.20/1.48  Demodulation         : 0.07
% 3.20/1.48  BG Simplification    : 0.02
% 3.20/1.48  Subsumption          : 0.11
% 3.20/1.48  Abstraction          : 0.02
% 3.20/1.48  MUC search           : 0.00
% 3.20/1.48  Cooper               : 0.00
% 3.20/1.48  Total                : 0.74
% 3.20/1.48  Index Insertion      : 0.00
% 3.20/1.48  Index Deletion       : 0.00
% 3.20/1.48  Index Matching       : 0.00
% 3.20/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
