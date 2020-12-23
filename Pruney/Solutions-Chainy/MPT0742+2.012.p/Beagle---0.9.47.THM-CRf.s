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
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 139 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 347 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_93,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_22,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,C_38)
      | ~ r1_tarski(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_4')
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_66,plain,(
    ! [A_41] :
      ( r1_tarski(k1_tarski(A_41),'#skF_4')
      | ~ r2_hidden(A_41,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_4')
      | ~ r2_hidden(A_42,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_98,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44,'#skF_3'),'#skF_4')
      | ~ r2_hidden(A_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v3_ordinal1(A_15)
      | ~ r2_hidden(A_15,B_16)
      | ~ v3_ordinal1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_101,plain,(
    ! [A_44] :
      ( v3_ordinal1('#skF_2'(A_44,'#skF_3'))
      | ~ v3_ordinal1('#skF_4')
      | ~ r2_hidden(A_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_104,plain,(
    ! [A_44] :
      ( v3_ordinal1('#skF_2'(A_44,'#skF_3'))
      | ~ r2_hidden(A_44,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_101])).

tff(c_28,plain,(
    ! [C_23] :
      ( v3_ordinal1('#skF_5'(C_23))
      | ~ r2_hidden(C_23,'#skF_3')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_5'(C_23),'#skF_3')
      | ~ r2_hidden(C_23,'#skF_3')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [B_19,A_17] :
      ( r2_hidden(B_19,A_17)
      | r1_ordinal1(A_17,B_19)
      | ~ v3_ordinal1(B_19)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [D_56,A_57,B_58] :
      ( ~ r2_hidden(D_56,'#skF_2'(A_57,B_58))
      | ~ r2_hidden(D_56,B_58)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_478,plain,(
    ! [B_81,B_82,A_83] :
      ( ~ r2_hidden(B_81,B_82)
      | ~ r2_hidden(A_83,B_82)
      | r1_ordinal1('#skF_2'(A_83,B_82),B_81)
      | ~ v3_ordinal1(B_81)
      | ~ v3_ordinal1('#skF_2'(A_83,B_82)) ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_24,plain,(
    ! [C_23] :
      ( ~ r1_ordinal1(C_23,'#skF_5'(C_23))
      | ~ r2_hidden(C_23,'#skF_3')
      | ~ v3_ordinal1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_492,plain,(
    ! [A_85,B_86] :
      ( ~ r2_hidden('#skF_2'(A_85,B_86),'#skF_3')
      | ~ r2_hidden('#skF_5'('#skF_2'(A_85,B_86)),B_86)
      | ~ r2_hidden(A_85,B_86)
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_85,B_86)))
      | ~ v3_ordinal1('#skF_2'(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_478,c_24])).

tff(c_558,plain,(
    ! [A_99] :
      ( ~ r2_hidden(A_99,'#skF_3')
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_99,'#skF_3')))
      | ~ r2_hidden('#skF_2'(A_99,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_99,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_492])).

tff(c_687,plain,(
    ! [A_112] :
      ( ~ r2_hidden(A_112,'#skF_3')
      | ~ r2_hidden('#skF_2'(A_112,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_112,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_28,c_558])).

tff(c_697,plain,(
    ! [A_113] :
      ( ~ v3_ordinal1('#skF_2'(A_113,'#skF_3'))
      | ~ r2_hidden(A_113,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_687])).

tff(c_706,plain,(
    ! [A_44] : ~ r2_hidden(A_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_697])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,
    ( r2_hidden('#skF_1'('#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_90,plain,(
    r2_hidden('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_85])).

tff(c_124,plain,(
    ! [A_51,B_52,A_53] :
      ( r1_tarski(A_51,B_52)
      | ~ r1_tarski(A_51,k1_tarski(A_53))
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_152,plain,(
    ! [A_59,B_60,A_61] :
      ( r1_tarski(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_61,B_60)
      | ~ r2_hidden(A_59,k1_tarski(A_61)) ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_190,plain,(
    ! [A_64] :
      ( r1_tarski(k1_tarski(A_64),'#skF_4')
      | ~ r2_hidden(A_64,k1_tarski('#skF_1'('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_90,c_152])).

tff(c_205,plain,
    ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_3')))),'#skF_4')
    | k1_tarski('#skF_1'('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_190])).

tff(c_238,plain,(
    k1_tarski('#skF_1'('#skF_3')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_65,plain,(
    ! [A_6] :
      ( r1_tarski(k1_tarski(A_6),'#skF_4')
      | ~ r2_hidden(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_254,plain,
    ( r1_tarski(k1_xboole_0,'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_65])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_408,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_399])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_408])).

tff(c_418,plain,(
    r2_hidden('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:25:42 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.38  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.78/1.38  
% 2.78/1.38  %Foreground sorts:
% 2.78/1.38  
% 2.78/1.38  
% 2.78/1.38  %Background operators:
% 2.78/1.38  
% 2.78/1.38  
% 2.78/1.38  %Foreground operators:
% 2.78/1.38  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.78/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.38  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.78/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.78/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.38  
% 2.78/1.40  tff(f_93, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 2.78/1.40  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.78/1.40  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.78/1.40  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.78/1.40  tff(f_62, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.78/1.40  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.78/1.40  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.40  tff(c_22, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.40  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.40  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_53, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, C_38) | ~r1_tarski(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.40  tff(c_60, plain, (![A_40]: (r1_tarski(A_40, '#skF_4') | ~r1_tarski(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_53])).
% 2.78/1.40  tff(c_66, plain, (![A_41]: (r1_tarski(k1_tarski(A_41), '#skF_4') | ~r2_hidden(A_41, '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.78/1.40  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.40  tff(c_74, plain, (![A_42]: (r2_hidden(A_42, '#skF_4') | ~r2_hidden(A_42, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_6])).
% 2.78/1.40  tff(c_98, plain, (![A_44]: (r2_hidden('#skF_2'(A_44, '#skF_3'), '#skF_4') | ~r2_hidden(A_44, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_74])).
% 2.78/1.40  tff(c_14, plain, (![A_15, B_16]: (v3_ordinal1(A_15) | ~r2_hidden(A_15, B_16) | ~v3_ordinal1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.78/1.40  tff(c_101, plain, (![A_44]: (v3_ordinal1('#skF_2'(A_44, '#skF_3')) | ~v3_ordinal1('#skF_4') | ~r2_hidden(A_44, '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_14])).
% 2.78/1.40  tff(c_104, plain, (![A_44]: (v3_ordinal1('#skF_2'(A_44, '#skF_3')) | ~r2_hidden(A_44, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_101])).
% 2.78/1.40  tff(c_28, plain, (![C_23]: (v3_ordinal1('#skF_5'(C_23)) | ~r2_hidden(C_23, '#skF_3') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_26, plain, (![C_23]: (r2_hidden('#skF_5'(C_23), '#skF_3') | ~r2_hidden(C_23, '#skF_3') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_16, plain, (![B_19, A_17]: (r2_hidden(B_19, A_17) | r1_ordinal1(A_17, B_19) | ~v3_ordinal1(B_19) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.40  tff(c_135, plain, (![D_56, A_57, B_58]: (~r2_hidden(D_56, '#skF_2'(A_57, B_58)) | ~r2_hidden(D_56, B_58) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.40  tff(c_478, plain, (![B_81, B_82, A_83]: (~r2_hidden(B_81, B_82) | ~r2_hidden(A_83, B_82) | r1_ordinal1('#skF_2'(A_83, B_82), B_81) | ~v3_ordinal1(B_81) | ~v3_ordinal1('#skF_2'(A_83, B_82)))), inference(resolution, [status(thm)], [c_16, c_135])).
% 2.78/1.40  tff(c_24, plain, (![C_23]: (~r1_ordinal1(C_23, '#skF_5'(C_23)) | ~r2_hidden(C_23, '#skF_3') | ~v3_ordinal1(C_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_492, plain, (![A_85, B_86]: (~r2_hidden('#skF_2'(A_85, B_86), '#skF_3') | ~r2_hidden('#skF_5'('#skF_2'(A_85, B_86)), B_86) | ~r2_hidden(A_85, B_86) | ~v3_ordinal1('#skF_5'('#skF_2'(A_85, B_86))) | ~v3_ordinal1('#skF_2'(A_85, B_86)))), inference(resolution, [status(thm)], [c_478, c_24])).
% 2.78/1.40  tff(c_558, plain, (![A_99]: (~r2_hidden(A_99, '#skF_3') | ~v3_ordinal1('#skF_5'('#skF_2'(A_99, '#skF_3'))) | ~r2_hidden('#skF_2'(A_99, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_99, '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_492])).
% 2.78/1.40  tff(c_687, plain, (![A_112]: (~r2_hidden(A_112, '#skF_3') | ~r2_hidden('#skF_2'(A_112, '#skF_3'), '#skF_3') | ~v3_ordinal1('#skF_2'(A_112, '#skF_3')))), inference(resolution, [status(thm)], [c_28, c_558])).
% 2.78/1.40  tff(c_697, plain, (![A_113]: (~v3_ordinal1('#skF_2'(A_113, '#skF_3')) | ~r2_hidden(A_113, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_687])).
% 2.78/1.40  tff(c_706, plain, (![A_44]: (~r2_hidden(A_44, '#skF_3'))), inference(resolution, [status(thm)], [c_104, c_697])).
% 2.78/1.40  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.40  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.40  tff(c_85, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_74])).
% 2.78/1.40  tff(c_90, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_18, c_85])).
% 2.78/1.40  tff(c_124, plain, (![A_51, B_52, A_53]: (r1_tarski(A_51, B_52) | ~r1_tarski(A_51, k1_tarski(A_53)) | ~r2_hidden(A_53, B_52))), inference(resolution, [status(thm)], [c_8, c_53])).
% 2.78/1.40  tff(c_152, plain, (![A_59, B_60, A_61]: (r1_tarski(k1_tarski(A_59), B_60) | ~r2_hidden(A_61, B_60) | ~r2_hidden(A_59, k1_tarski(A_61)))), inference(resolution, [status(thm)], [c_8, c_124])).
% 2.78/1.40  tff(c_190, plain, (![A_64]: (r1_tarski(k1_tarski(A_64), '#skF_4') | ~r2_hidden(A_64, k1_tarski('#skF_1'('#skF_3'))))), inference(resolution, [status(thm)], [c_90, c_152])).
% 2.78/1.40  tff(c_205, plain, (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_3')))), '#skF_4') | k1_tarski('#skF_1'('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_190])).
% 2.78/1.40  tff(c_238, plain, (k1_tarski('#skF_1'('#skF_3'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 2.78/1.40  tff(c_65, plain, (![A_6]: (r1_tarski(k1_tarski(A_6), '#skF_4') | ~r2_hidden(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.78/1.40  tff(c_254, plain, (r1_tarski(k1_xboole_0, '#skF_4') | ~r2_hidden('#skF_1'('#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_238, c_65])).
% 2.78/1.40  tff(c_399, plain, (~r2_hidden('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_254])).
% 2.78/1.40  tff(c_408, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_399])).
% 2.78/1.40  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_408])).
% 2.78/1.40  tff(c_418, plain, (r2_hidden('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_254])).
% 2.78/1.40  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_706, c_418])).
% 2.78/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  Inference rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Ref     : 0
% 2.78/1.40  #Sup     : 137
% 2.78/1.40  #Fact    : 0
% 2.78/1.40  #Define  : 0
% 2.78/1.40  #Split   : 5
% 2.78/1.40  #Chain   : 0
% 2.78/1.40  #Close   : 0
% 2.78/1.40  
% 2.78/1.40  Ordering : KBO
% 2.78/1.40  
% 2.78/1.40  Simplification rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Subsume      : 52
% 2.78/1.40  #Demod        : 29
% 2.78/1.40  #Tautology    : 16
% 2.78/1.40  #SimpNegUnit  : 10
% 2.78/1.40  #BackRed      : 4
% 2.78/1.40  
% 2.78/1.40  #Partial instantiations: 0
% 2.78/1.40  #Strategies tried      : 1
% 2.78/1.40  
% 2.78/1.40  Timing (in seconds)
% 2.78/1.40  ----------------------
% 2.78/1.40  Preprocessing        : 0.27
% 2.78/1.40  Parsing              : 0.15
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.35
% 2.78/1.40  Inferencing          : 0.14
% 2.78/1.40  Reduction            : 0.08
% 2.78/1.40  Demodulation         : 0.05
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.09
% 2.78/1.40  Abstraction          : 0.01
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.66
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
