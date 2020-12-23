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
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 159 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_72,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_366,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_93)
      | r2_hidden('#skF_2'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_703,plain,(
    ! [B_109,A_110] :
      ( ~ r1_tarski(B_109,'#skF_1'(A_110,B_109))
      | r2_hidden('#skF_2'(A_110,B_109),A_110)
      | B_109 = A_110 ) ),
    inference(resolution,[status(thm)],[c_366,c_26])).

tff(c_711,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_2'(A_110,k1_xboole_0),A_110)
      | k1_xboole_0 = A_110 ) ),
    inference(resolution,[status(thm)],[c_12,c_703])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_84,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_5')
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [A_52] :
      ( r2_hidden(A_52,'#skF_5')
      | ~ r1_tarski(k1_tarski(A_52),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105,c_14])).

tff(c_120,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,'#skF_5')
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_114])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v3_ordinal1(A_17)
      | ~ r2_hidden(A_17,B_18)
      | ~ v3_ordinal1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_123,plain,(
    ! [A_53] :
      ( v3_ordinal1(A_53)
      | ~ v3_ordinal1('#skF_5')
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_120,c_22])).

tff(c_132,plain,(
    ! [A_55] :
      ( v3_ordinal1(A_55)
      | ~ r2_hidden(A_55,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_123])).

tff(c_140,plain,(
    ! [A_10] :
      ( v3_ordinal1('#skF_3'(A_10,'#skF_4'))
      | ~ r2_hidden(A_10,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_38,plain,(
    ! [C_27] :
      ( v3_ordinal1('#skF_6'(C_27))
      | ~ r2_hidden(C_27,'#skF_4')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    ! [C_27] :
      ( r2_hidden('#skF_6'(C_27),'#skF_4')
      | ~ r2_hidden(C_27,'#skF_4')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( r2_hidden(B_21,A_19)
      | r1_ordinal1(A_19,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_239,plain,(
    ! [D_72,A_73,B_74] :
      ( ~ r2_hidden(D_72,'#skF_3'(A_73,B_74))
      | ~ r2_hidden(D_72,B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1716,plain,(
    ! [B_178,B_179,A_180] :
      ( ~ r2_hidden(B_178,B_179)
      | ~ r2_hidden(A_180,B_179)
      | r1_ordinal1('#skF_3'(A_180,B_179),B_178)
      | ~ v3_ordinal1(B_178)
      | ~ v3_ordinal1('#skF_3'(A_180,B_179)) ) ),
    inference(resolution,[status(thm)],[c_24,c_239])).

tff(c_34,plain,(
    ! [C_27] :
      ( ~ r1_ordinal1(C_27,'#skF_6'(C_27))
      | ~ r2_hidden(C_27,'#skF_4')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1724,plain,(
    ! [A_183,B_184] :
      ( ~ r2_hidden('#skF_3'(A_183,B_184),'#skF_4')
      | ~ r2_hidden('#skF_6'('#skF_3'(A_183,B_184)),B_184)
      | ~ r2_hidden(A_183,B_184)
      | ~ v3_ordinal1('#skF_6'('#skF_3'(A_183,B_184)))
      | ~ v3_ordinal1('#skF_3'(A_183,B_184)) ) ),
    inference(resolution,[status(thm)],[c_1716,c_34])).

tff(c_1960,plain,(
    ! [A_198] :
      ( ~ r2_hidden(A_198,'#skF_4')
      | ~ v3_ordinal1('#skF_6'('#skF_3'(A_198,'#skF_4')))
      | ~ r2_hidden('#skF_3'(A_198,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_3'(A_198,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1724])).

tff(c_1965,plain,(
    ! [A_199] :
      ( ~ r2_hidden(A_199,'#skF_4')
      | ~ r2_hidden('#skF_3'(A_199,'#skF_4'),'#skF_4')
      | ~ v3_ordinal1('#skF_3'(A_199,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1960])).

tff(c_1975,plain,(
    ! [A_200] :
      ( ~ v3_ordinal1('#skF_3'(A_200,'#skF_4'))
      | ~ r2_hidden(A_200,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_1965])).

tff(c_1991,plain,(
    ! [A_201] : ~ r2_hidden(A_201,'#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_1975])).

tff(c_2011,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_711,c_1991])).

tff(c_2046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.74  
% 4.25/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.74  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1 > #skF_6
% 4.25/1.74  
% 4.25/1.74  %Foreground sorts:
% 4.25/1.74  
% 4.25/1.74  
% 4.25/1.74  %Background operators:
% 4.25/1.74  
% 4.25/1.74  
% 4.25/1.74  %Foreground operators:
% 4.25/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.25/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.25/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.25/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.25/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.25/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.25/1.74  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.25/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.25/1.74  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.25/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.25/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.25/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.25/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.25/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.25/1.74  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.25/1.74  
% 4.25/1.75  tff(f_99, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 4.25/1.75  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.25/1.75  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.25/1.75  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.25/1.75  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.25/1.75  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.25/1.75  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.25/1.75  tff(f_63, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.25/1.75  tff(f_72, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.25/1.75  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.25/1.75  tff(c_366, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), B_93) | r2_hidden('#skF_2'(A_92, B_93), A_92) | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.25/1.75  tff(c_26, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.25/1.75  tff(c_703, plain, (![B_109, A_110]: (~r1_tarski(B_109, '#skF_1'(A_110, B_109)) | r2_hidden('#skF_2'(A_110, B_109), A_110) | B_109=A_110)), inference(resolution, [status(thm)], [c_366, c_26])).
% 4.25/1.75  tff(c_711, plain, (![A_110]: (r2_hidden('#skF_2'(A_110, k1_xboole_0), A_110) | k1_xboole_0=A_110)), inference(resolution, [status(thm)], [c_12, c_703])).
% 4.25/1.75  tff(c_20, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.25/1.75  tff(c_32, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.25/1.75  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_84, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.25/1.75  tff(c_105, plain, (![A_51]: (r1_tarski(A_51, '#skF_5') | ~r1_tarski(A_51, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_84])).
% 4.25/1.75  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.25/1.75  tff(c_114, plain, (![A_52]: (r2_hidden(A_52, '#skF_5') | ~r1_tarski(k1_tarski(A_52), '#skF_4'))), inference(resolution, [status(thm)], [c_105, c_14])).
% 4.25/1.75  tff(c_120, plain, (![A_53]: (r2_hidden(A_53, '#skF_5') | ~r2_hidden(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_114])).
% 4.25/1.75  tff(c_22, plain, (![A_17, B_18]: (v3_ordinal1(A_17) | ~r2_hidden(A_17, B_18) | ~v3_ordinal1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.25/1.75  tff(c_123, plain, (![A_53]: (v3_ordinal1(A_53) | ~v3_ordinal1('#skF_5') | ~r2_hidden(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_120, c_22])).
% 4.25/1.75  tff(c_132, plain, (![A_55]: (v3_ordinal1(A_55) | ~r2_hidden(A_55, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_123])).
% 4.25/1.75  tff(c_140, plain, (![A_10]: (v3_ordinal1('#skF_3'(A_10, '#skF_4')) | ~r2_hidden(A_10, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_132])).
% 4.25/1.75  tff(c_38, plain, (![C_27]: (v3_ordinal1('#skF_6'(C_27)) | ~r2_hidden(C_27, '#skF_4') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_36, plain, (![C_27]: (r2_hidden('#skF_6'(C_27), '#skF_4') | ~r2_hidden(C_27, '#skF_4') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_24, plain, (![B_21, A_19]: (r2_hidden(B_21, A_19) | r1_ordinal1(A_19, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.25/1.75  tff(c_239, plain, (![D_72, A_73, B_74]: (~r2_hidden(D_72, '#skF_3'(A_73, B_74)) | ~r2_hidden(D_72, B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.25/1.75  tff(c_1716, plain, (![B_178, B_179, A_180]: (~r2_hidden(B_178, B_179) | ~r2_hidden(A_180, B_179) | r1_ordinal1('#skF_3'(A_180, B_179), B_178) | ~v3_ordinal1(B_178) | ~v3_ordinal1('#skF_3'(A_180, B_179)))), inference(resolution, [status(thm)], [c_24, c_239])).
% 4.25/1.75  tff(c_34, plain, (![C_27]: (~r1_ordinal1(C_27, '#skF_6'(C_27)) | ~r2_hidden(C_27, '#skF_4') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.25/1.75  tff(c_1724, plain, (![A_183, B_184]: (~r2_hidden('#skF_3'(A_183, B_184), '#skF_4') | ~r2_hidden('#skF_6'('#skF_3'(A_183, B_184)), B_184) | ~r2_hidden(A_183, B_184) | ~v3_ordinal1('#skF_6'('#skF_3'(A_183, B_184))) | ~v3_ordinal1('#skF_3'(A_183, B_184)))), inference(resolution, [status(thm)], [c_1716, c_34])).
% 4.25/1.75  tff(c_1960, plain, (![A_198]: (~r2_hidden(A_198, '#skF_4') | ~v3_ordinal1('#skF_6'('#skF_3'(A_198, '#skF_4'))) | ~r2_hidden('#skF_3'(A_198, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_3'(A_198, '#skF_4')))), inference(resolution, [status(thm)], [c_36, c_1724])).
% 4.25/1.75  tff(c_1965, plain, (![A_199]: (~r2_hidden(A_199, '#skF_4') | ~r2_hidden('#skF_3'(A_199, '#skF_4'), '#skF_4') | ~v3_ordinal1('#skF_3'(A_199, '#skF_4')))), inference(resolution, [status(thm)], [c_38, c_1960])).
% 4.25/1.75  tff(c_1975, plain, (![A_200]: (~v3_ordinal1('#skF_3'(A_200, '#skF_4')) | ~r2_hidden(A_200, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1965])).
% 4.25/1.75  tff(c_1991, plain, (![A_201]: (~r2_hidden(A_201, '#skF_4'))), inference(resolution, [status(thm)], [c_140, c_1975])).
% 4.25/1.75  tff(c_2011, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_711, c_1991])).
% 4.25/1.75  tff(c_2046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2011])).
% 4.25/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.75  
% 4.25/1.75  Inference rules
% 4.25/1.75  ----------------------
% 4.25/1.75  #Ref     : 0
% 4.25/1.75  #Sup     : 395
% 4.25/1.75  #Fact    : 0
% 4.25/1.75  #Define  : 0
% 4.25/1.75  #Split   : 5
% 4.25/1.75  #Chain   : 0
% 4.25/1.75  #Close   : 0
% 4.25/1.75  
% 4.25/1.75  Ordering : KBO
% 4.25/1.75  
% 4.25/1.75  Simplification rules
% 4.25/1.75  ----------------------
% 4.25/1.75  #Subsume      : 120
% 4.25/1.75  #Demod        : 67
% 4.25/1.75  #Tautology    : 40
% 4.25/1.75  #SimpNegUnit  : 17
% 4.25/1.75  #BackRed      : 23
% 4.25/1.75  
% 4.25/1.75  #Partial instantiations: 0
% 4.25/1.75  #Strategies tried      : 1
% 4.25/1.75  
% 4.25/1.75  Timing (in seconds)
% 4.25/1.75  ----------------------
% 4.25/1.76  Preprocessing        : 0.28
% 4.25/1.76  Parsing              : 0.15
% 4.25/1.76  CNF conversion       : 0.02
% 4.25/1.76  Main loop            : 0.70
% 4.25/1.76  Inferencing          : 0.27
% 4.25/1.76  Reduction            : 0.16
% 4.25/1.76  Demodulation         : 0.10
% 4.25/1.76  BG Simplification    : 0.03
% 4.25/1.76  Subsumption          : 0.18
% 4.25/1.76  Abstraction          : 0.03
% 4.25/1.76  MUC search           : 0.00
% 4.25/1.76  Cooper               : 0.00
% 4.25/1.76  Total                : 1.01
% 4.25/1.76  Index Insertion      : 0.00
% 4.25/1.76  Index Deletion       : 0.00
% 4.25/1.76  Index Matching       : 0.00
% 4.25/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
