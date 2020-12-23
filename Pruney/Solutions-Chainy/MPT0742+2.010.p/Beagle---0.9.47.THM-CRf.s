%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 179 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_36,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_49,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_84,plain,(
    ! [D_41,B_42,A_43] :
      ( r2_hidden(D_41,B_42)
      | ~ r2_hidden(D_41,k3_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_6')
      | ~ r2_hidden(D_44,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_84])).

tff(c_122,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_4'(A_46,'#skF_5'),'#skF_6')
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( v3_ordinal1(A_18)
      | ~ r2_hidden(A_18,B_19)
      | ~ v3_ordinal1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [A_46] :
      ( v3_ordinal1('#skF_4'(A_46,'#skF_5'))
      | ~ v3_ordinal1('#skF_6')
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_122,c_28])).

tff(c_128,plain,(
    ! [A_46] :
      ( v3_ordinal1('#skF_4'(A_46,'#skF_5'))
      | ~ r2_hidden(A_46,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_125])).

tff(c_42,plain,(
    ! [C_26] :
      ( v3_ordinal1('#skF_7'(C_26))
      | ~ r2_hidden(C_26,'#skF_5')
      | ~ v3_ordinal1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [C_26] :
      ( r2_hidden('#skF_7'(C_26),'#skF_5')
      | ~ r2_hidden(C_26,'#skF_5')
      | ~ v3_ordinal1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [B_22,A_20] :
      ( r2_hidden(B_22,A_20)
      | r1_ordinal1(A_20,B_22)
      | ~ v3_ordinal1(B_22)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_218,plain,(
    ! [D_57,A_58,B_59] :
      ( ~ r2_hidden(D_57,'#skF_4'(A_58,B_59))
      | ~ r2_hidden(D_57,B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1506,plain,(
    ! [B_203,B_204,A_205] :
      ( ~ r2_hidden(B_203,B_204)
      | ~ r2_hidden(A_205,B_204)
      | r1_ordinal1('#skF_4'(A_205,B_204),B_203)
      | ~ v3_ordinal1(B_203)
      | ~ v3_ordinal1('#skF_4'(A_205,B_204)) ) ),
    inference(resolution,[status(thm)],[c_30,c_218])).

tff(c_38,plain,(
    ! [C_26] :
      ( ~ r1_ordinal1(C_26,'#skF_7'(C_26))
      | ~ r2_hidden(C_26,'#skF_5')
      | ~ v3_ordinal1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1551,plain,(
    ! [A_210,B_211] :
      ( ~ r2_hidden('#skF_4'(A_210,B_211),'#skF_5')
      | ~ r2_hidden('#skF_7'('#skF_4'(A_210,B_211)),B_211)
      | ~ r2_hidden(A_210,B_211)
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_210,B_211)))
      | ~ v3_ordinal1('#skF_4'(A_210,B_211)) ) ),
    inference(resolution,[status(thm)],[c_1506,c_38])).

tff(c_1784,plain,(
    ! [A_234] :
      ( ~ r2_hidden(A_234,'#skF_5')
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_234,'#skF_5')))
      | ~ r2_hidden('#skF_4'(A_234,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_234,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1551])).

tff(c_1789,plain,(
    ! [A_235] :
      ( ~ r2_hidden(A_235,'#skF_5')
      | ~ r2_hidden('#skF_4'(A_235,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_235,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1784])).

tff(c_1799,plain,(
    ! [A_236] :
      ( ~ v3_ordinal1('#skF_4'(A_236,'#skF_5'))
      | ~ r2_hidden(A_236,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_1789])).

tff(c_1808,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_1799])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,A_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_55,B_56)),A_55)
      | k3_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_201,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_183])).

tff(c_206,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_201])).

tff(c_207,plain,(
    r2_hidden('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_206])).

tff(c_1811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1808,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.66  
% 3.84/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.66  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.84/1.66  
% 3.84/1.66  %Foreground sorts:
% 3.84/1.66  
% 3.84/1.66  
% 3.84/1.66  %Background operators:
% 3.84/1.66  
% 3.84/1.66  
% 3.84/1.66  %Foreground operators:
% 3.84/1.66  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.84/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.84/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.66  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.84/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.84/1.66  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.84/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.66  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.84/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.84/1.66  
% 3.84/1.67  tff(f_96, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 3.84/1.67  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.84/1.67  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.84/1.67  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.84/1.67  tff(f_65, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.84/1.67  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.84/1.67  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.84/1.67  tff(c_36, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.84/1.67  tff(c_34, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_49, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.84/1.67  tff(c_53, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_34, c_49])).
% 3.84/1.67  tff(c_84, plain, (![D_41, B_42, A_43]: (r2_hidden(D_41, B_42) | ~r2_hidden(D_41, k3_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.84/1.67  tff(c_98, plain, (![D_44]: (r2_hidden(D_44, '#skF_6') | ~r2_hidden(D_44, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_84])).
% 3.84/1.67  tff(c_122, plain, (![A_46]: (r2_hidden('#skF_4'(A_46, '#skF_5'), '#skF_6') | ~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_98])).
% 3.84/1.67  tff(c_28, plain, (![A_18, B_19]: (v3_ordinal1(A_18) | ~r2_hidden(A_18, B_19) | ~v3_ordinal1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.84/1.67  tff(c_125, plain, (![A_46]: (v3_ordinal1('#skF_4'(A_46, '#skF_5')) | ~v3_ordinal1('#skF_6') | ~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_122, c_28])).
% 3.84/1.67  tff(c_128, plain, (![A_46]: (v3_ordinal1('#skF_4'(A_46, '#skF_5')) | ~r2_hidden(A_46, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_125])).
% 3.84/1.67  tff(c_42, plain, (![C_26]: (v3_ordinal1('#skF_7'(C_26)) | ~r2_hidden(C_26, '#skF_5') | ~v3_ordinal1(C_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_40, plain, (![C_26]: (r2_hidden('#skF_7'(C_26), '#skF_5') | ~r2_hidden(C_26, '#skF_5') | ~v3_ordinal1(C_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_30, plain, (![B_22, A_20]: (r2_hidden(B_22, A_20) | r1_ordinal1(A_20, B_22) | ~v3_ordinal1(B_22) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.84/1.67  tff(c_218, plain, (![D_57, A_58, B_59]: (~r2_hidden(D_57, '#skF_4'(A_58, B_59)) | ~r2_hidden(D_57, B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.84/1.67  tff(c_1506, plain, (![B_203, B_204, A_205]: (~r2_hidden(B_203, B_204) | ~r2_hidden(A_205, B_204) | r1_ordinal1('#skF_4'(A_205, B_204), B_203) | ~v3_ordinal1(B_203) | ~v3_ordinal1('#skF_4'(A_205, B_204)))), inference(resolution, [status(thm)], [c_30, c_218])).
% 3.84/1.67  tff(c_38, plain, (![C_26]: (~r1_ordinal1(C_26, '#skF_7'(C_26)) | ~r2_hidden(C_26, '#skF_5') | ~v3_ordinal1(C_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_1551, plain, (![A_210, B_211]: (~r2_hidden('#skF_4'(A_210, B_211), '#skF_5') | ~r2_hidden('#skF_7'('#skF_4'(A_210, B_211)), B_211) | ~r2_hidden(A_210, B_211) | ~v3_ordinal1('#skF_7'('#skF_4'(A_210, B_211))) | ~v3_ordinal1('#skF_4'(A_210, B_211)))), inference(resolution, [status(thm)], [c_1506, c_38])).
% 3.84/1.67  tff(c_1784, plain, (![A_234]: (~r2_hidden(A_234, '#skF_5') | ~v3_ordinal1('#skF_7'('#skF_4'(A_234, '#skF_5'))) | ~r2_hidden('#skF_4'(A_234, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_234, '#skF_5')))), inference(resolution, [status(thm)], [c_40, c_1551])).
% 3.84/1.67  tff(c_1789, plain, (![A_235]: (~r2_hidden(A_235, '#skF_5') | ~r2_hidden('#skF_4'(A_235, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_235, '#skF_5')))), inference(resolution, [status(thm)], [c_42, c_1784])).
% 3.84/1.67  tff(c_1799, plain, (![A_236]: (~v3_ordinal1('#skF_4'(A_236, '#skF_5')) | ~r2_hidden(A_236, '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_1789])).
% 3.84/1.67  tff(c_1808, plain, (![A_46]: (~r2_hidden(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_128, c_1799])).
% 3.84/1.67  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.67  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.84/1.67  tff(c_70, plain, (![D_38, A_39, B_40]: (r2_hidden(D_38, A_39) | ~r2_hidden(D_38, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.84/1.67  tff(c_183, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(k3_xboole_0(A_55, B_56)), A_55) | k3_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_70])).
% 3.84/1.67  tff(c_201, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_53, c_183])).
% 3.84/1.67  tff(c_206, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_201])).
% 3.84/1.67  tff(c_207, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_206])).
% 3.84/1.67  tff(c_1811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1808, c_207])).
% 3.84/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.67  
% 3.84/1.67  Inference rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Ref     : 0
% 3.84/1.67  #Sup     : 355
% 3.84/1.67  #Fact    : 0
% 3.84/1.67  #Define  : 0
% 3.84/1.67  #Split   : 1
% 3.84/1.67  #Chain   : 0
% 3.84/1.67  #Close   : 0
% 3.84/1.67  
% 3.84/1.67  Ordering : KBO
% 3.84/1.67  
% 3.84/1.67  Simplification rules
% 3.84/1.67  ----------------------
% 3.84/1.67  #Subsume      : 151
% 3.84/1.67  #Demod        : 172
% 3.84/1.67  #Tautology    : 27
% 3.84/1.67  #SimpNegUnit  : 13
% 3.84/1.67  #BackRed      : 1
% 3.84/1.67  
% 3.84/1.67  #Partial instantiations: 0
% 3.84/1.67  #Strategies tried      : 1
% 3.84/1.67  
% 3.84/1.67  Timing (in seconds)
% 3.84/1.67  ----------------------
% 3.84/1.68  Preprocessing        : 0.31
% 3.84/1.68  Parsing              : 0.16
% 3.84/1.68  CNF conversion       : 0.02
% 3.84/1.68  Main loop            : 0.61
% 3.84/1.68  Inferencing          : 0.25
% 3.84/1.68  Reduction            : 0.15
% 3.84/1.68  Demodulation         : 0.10
% 3.84/1.68  BG Simplification    : 0.03
% 3.84/1.68  Subsumption          : 0.14
% 3.84/1.68  Abstraction          : 0.03
% 3.84/1.68  MUC search           : 0.00
% 3.84/1.68  Cooper               : 0.00
% 3.84/1.68  Total                : 0.95
% 3.84/1.68  Index Insertion      : 0.00
% 3.84/1.68  Index Deletion       : 0.00
% 3.84/1.68  Index Matching       : 0.00
% 3.84/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
