%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:08 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 197 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_375,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),B_98)
      | r2_hidden('#skF_3'(A_97,B_98),A_97)
      | B_98 = A_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_706,plain,(
    ! [B_132,A_133] :
      ( ~ r1_tarski(B_132,'#skF_2'(A_133,B_132))
      | r2_hidden('#skF_3'(A_133,B_132),A_133)
      | B_132 = A_133 ) ),
    inference(resolution,[status(thm)],[c_375,c_26])).

tff(c_710,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_3'(A_133,k1_xboole_0),A_133)
      | k1_xboole_0 = A_133 ) ),
    inference(resolution,[status(thm)],[c_16,c_706])).

tff(c_62,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_40] : r1_tarski(A_40,A_40) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_32,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_4'(A_10,B_11),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden('#skF_4'(A_65,B_66),B_67)
      | ~ r1_tarski(B_66,B_67)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1864,plain,(
    ! [A_260,B_261,B_262,B_263] :
      ( r2_hidden('#skF_4'(A_260,B_261),B_262)
      | ~ r1_tarski(B_263,B_262)
      | ~ r1_tarski(B_261,B_263)
      | ~ r2_hidden(A_260,B_261) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_1885,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_4'(A_267,B_268),'#skF_6')
      | ~ r1_tarski(B_268,'#skF_5')
      | ~ r2_hidden(A_267,B_268) ) ),
    inference(resolution,[status(thm)],[c_30,c_1864])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v3_ordinal1(A_17)
      | ~ r2_hidden(A_17,B_18)
      | ~ v3_ordinal1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1897,plain,(
    ! [A_267,B_268] :
      ( v3_ordinal1('#skF_4'(A_267,B_268))
      | ~ v3_ordinal1('#skF_6')
      | ~ r1_tarski(B_268,'#skF_5')
      | ~ r2_hidden(A_267,B_268) ) ),
    inference(resolution,[status(thm)],[c_1885,c_22])).

tff(c_1906,plain,(
    ! [A_267,B_268] :
      ( v3_ordinal1('#skF_4'(A_267,B_268))
      | ~ r1_tarski(B_268,'#skF_5')
      | ~ r2_hidden(A_267,B_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1897])).

tff(c_112,plain,(
    ! [A_10,B_11,B_50] :
      ( r2_hidden('#skF_4'(A_10,B_11),B_50)
      | ~ r1_tarski(B_11,B_50)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_38,plain,(
    ! [C_27] :
      ( v3_ordinal1('#skF_7'(C_27))
      | ~ r2_hidden(C_27,'#skF_5')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ! [C_27] :
      ( r2_hidden('#skF_7'(C_27),'#skF_5')
      | ~ r2_hidden(C_27,'#skF_5')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( r2_hidden(B_21,A_19)
      | r1_ordinal1(A_19,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,(
    ! [D_62,A_63,B_64] :
      ( ~ r2_hidden(D_62,'#skF_4'(A_63,B_64))
      | ~ r2_hidden(D_62,B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2199,plain,(
    ! [B_301,B_302,A_303] :
      ( ~ r2_hidden(B_301,B_302)
      | ~ r2_hidden(A_303,B_302)
      | r1_ordinal1('#skF_4'(A_303,B_302),B_301)
      | ~ v3_ordinal1(B_301)
      | ~ v3_ordinal1('#skF_4'(A_303,B_302)) ) ),
    inference(resolution,[status(thm)],[c_24,c_155])).

tff(c_34,plain,(
    ! [C_27] :
      ( ~ r1_ordinal1(C_27,'#skF_7'(C_27))
      | ~ r2_hidden(C_27,'#skF_5')
      | ~ v3_ordinal1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2251,plain,(
    ! [A_309,B_310] :
      ( ~ r2_hidden('#skF_4'(A_309,B_310),'#skF_5')
      | ~ r2_hidden('#skF_7'('#skF_4'(A_309,B_310)),B_310)
      | ~ r2_hidden(A_309,B_310)
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_309,B_310)))
      | ~ v3_ordinal1('#skF_4'(A_309,B_310)) ) ),
    inference(resolution,[status(thm)],[c_2199,c_34])).

tff(c_2453,plain,(
    ! [A_333] :
      ( ~ r2_hidden(A_333,'#skF_5')
      | ~ v3_ordinal1('#skF_7'('#skF_4'(A_333,'#skF_5')))
      | ~ r2_hidden('#skF_4'(A_333,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_333,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_2251])).

tff(c_2459,plain,(
    ! [A_335] :
      ( ~ r2_hidden(A_335,'#skF_5')
      | ~ r2_hidden('#skF_4'(A_335,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_4'(A_335,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2453])).

tff(c_2467,plain,(
    ! [A_10] :
      ( ~ v3_ordinal1('#skF_4'(A_10,'#skF_5'))
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_10,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_112,c_2459])).

tff(c_2483,plain,(
    ! [A_336] :
      ( ~ v3_ordinal1('#skF_4'(A_336,'#skF_5'))
      | ~ r2_hidden(A_336,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2467])).

tff(c_2487,plain,(
    ! [A_267] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_267,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1906,c_2483])).

tff(c_2501,plain,(
    ! [A_337] : ~ r2_hidden(A_337,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2487])).

tff(c_2565,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_710,c_2501])).

tff(c_2629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.86  
% 4.54/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.86  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.54/1.86  
% 4.54/1.86  %Foreground sorts:
% 4.54/1.86  
% 4.54/1.86  
% 4.54/1.86  %Background operators:
% 4.54/1.86  
% 4.54/1.86  
% 4.54/1.86  %Foreground operators:
% 4.54/1.86  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.54/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.54/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.86  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.54/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.54/1.86  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.54/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.54/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.54/1.86  
% 4.54/1.87  tff(f_96, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 4.54/1.87  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.54/1.87  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.54/1.87  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.54/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.54/1.87  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.54/1.87  tff(f_60, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.54/1.87  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.54/1.87  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.54/1.87  tff(c_375, plain, (![A_97, B_98]: (r2_hidden('#skF_2'(A_97, B_98), B_98) | r2_hidden('#skF_3'(A_97, B_98), A_97) | B_98=A_97)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.87  tff(c_26, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.54/1.87  tff(c_706, plain, (![B_132, A_133]: (~r1_tarski(B_132, '#skF_2'(A_133, B_132)) | r2_hidden('#skF_3'(A_133, B_132), A_133) | B_132=A_133)), inference(resolution, [status(thm)], [c_375, c_26])).
% 4.54/1.87  tff(c_710, plain, (![A_133]: (r2_hidden('#skF_3'(A_133, k1_xboole_0), A_133) | k1_xboole_0=A_133)), inference(resolution, [status(thm)], [c_16, c_706])).
% 4.54/1.87  tff(c_62, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.87  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.87  tff(c_73, plain, (![A_40]: (r1_tarski(A_40, A_40))), inference(resolution, [status(thm)], [c_62, c_4])).
% 4.54/1.87  tff(c_32, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_30, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_20, plain, (![A_10, B_11]: (r2_hidden('#skF_4'(A_10, B_11), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.54/1.87  tff(c_103, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.87  tff(c_172, plain, (![A_65, B_66, B_67]: (r2_hidden('#skF_4'(A_65, B_66), B_67) | ~r1_tarski(B_66, B_67) | ~r2_hidden(A_65, B_66))), inference(resolution, [status(thm)], [c_20, c_103])).
% 4.54/1.87  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.87  tff(c_1864, plain, (![A_260, B_261, B_262, B_263]: (r2_hidden('#skF_4'(A_260, B_261), B_262) | ~r1_tarski(B_263, B_262) | ~r1_tarski(B_261, B_263) | ~r2_hidden(A_260, B_261))), inference(resolution, [status(thm)], [c_172, c_2])).
% 4.54/1.87  tff(c_1885, plain, (![A_267, B_268]: (r2_hidden('#skF_4'(A_267, B_268), '#skF_6') | ~r1_tarski(B_268, '#skF_5') | ~r2_hidden(A_267, B_268))), inference(resolution, [status(thm)], [c_30, c_1864])).
% 4.54/1.87  tff(c_22, plain, (![A_17, B_18]: (v3_ordinal1(A_17) | ~r2_hidden(A_17, B_18) | ~v3_ordinal1(B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.54/1.87  tff(c_1897, plain, (![A_267, B_268]: (v3_ordinal1('#skF_4'(A_267, B_268)) | ~v3_ordinal1('#skF_6') | ~r1_tarski(B_268, '#skF_5') | ~r2_hidden(A_267, B_268))), inference(resolution, [status(thm)], [c_1885, c_22])).
% 4.54/1.87  tff(c_1906, plain, (![A_267, B_268]: (v3_ordinal1('#skF_4'(A_267, B_268)) | ~r1_tarski(B_268, '#skF_5') | ~r2_hidden(A_267, B_268))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1897])).
% 4.54/1.87  tff(c_112, plain, (![A_10, B_11, B_50]: (r2_hidden('#skF_4'(A_10, B_11), B_50) | ~r1_tarski(B_11, B_50) | ~r2_hidden(A_10, B_11))), inference(resolution, [status(thm)], [c_20, c_103])).
% 4.54/1.87  tff(c_38, plain, (![C_27]: (v3_ordinal1('#skF_7'(C_27)) | ~r2_hidden(C_27, '#skF_5') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_36, plain, (![C_27]: (r2_hidden('#skF_7'(C_27), '#skF_5') | ~r2_hidden(C_27, '#skF_5') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_24, plain, (![B_21, A_19]: (r2_hidden(B_21, A_19) | r1_ordinal1(A_19, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.54/1.87  tff(c_155, plain, (![D_62, A_63, B_64]: (~r2_hidden(D_62, '#skF_4'(A_63, B_64)) | ~r2_hidden(D_62, B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.54/1.87  tff(c_2199, plain, (![B_301, B_302, A_303]: (~r2_hidden(B_301, B_302) | ~r2_hidden(A_303, B_302) | r1_ordinal1('#skF_4'(A_303, B_302), B_301) | ~v3_ordinal1(B_301) | ~v3_ordinal1('#skF_4'(A_303, B_302)))), inference(resolution, [status(thm)], [c_24, c_155])).
% 4.54/1.87  tff(c_34, plain, (![C_27]: (~r1_ordinal1(C_27, '#skF_7'(C_27)) | ~r2_hidden(C_27, '#skF_5') | ~v3_ordinal1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.54/1.87  tff(c_2251, plain, (![A_309, B_310]: (~r2_hidden('#skF_4'(A_309, B_310), '#skF_5') | ~r2_hidden('#skF_7'('#skF_4'(A_309, B_310)), B_310) | ~r2_hidden(A_309, B_310) | ~v3_ordinal1('#skF_7'('#skF_4'(A_309, B_310))) | ~v3_ordinal1('#skF_4'(A_309, B_310)))), inference(resolution, [status(thm)], [c_2199, c_34])).
% 4.54/1.87  tff(c_2453, plain, (![A_333]: (~r2_hidden(A_333, '#skF_5') | ~v3_ordinal1('#skF_7'('#skF_4'(A_333, '#skF_5'))) | ~r2_hidden('#skF_4'(A_333, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_333, '#skF_5')))), inference(resolution, [status(thm)], [c_36, c_2251])).
% 4.54/1.87  tff(c_2459, plain, (![A_335]: (~r2_hidden(A_335, '#skF_5') | ~r2_hidden('#skF_4'(A_335, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_4'(A_335, '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_2453])).
% 4.54/1.87  tff(c_2467, plain, (![A_10]: (~v3_ordinal1('#skF_4'(A_10, '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_10, '#skF_5'))), inference(resolution, [status(thm)], [c_112, c_2459])).
% 4.54/1.87  tff(c_2483, plain, (![A_336]: (~v3_ordinal1('#skF_4'(A_336, '#skF_5')) | ~r2_hidden(A_336, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2467])).
% 4.54/1.87  tff(c_2487, plain, (![A_267]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_267, '#skF_5'))), inference(resolution, [status(thm)], [c_1906, c_2483])).
% 4.54/1.87  tff(c_2501, plain, (![A_337]: (~r2_hidden(A_337, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2487])).
% 4.54/1.87  tff(c_2565, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_710, c_2501])).
% 4.54/1.87  tff(c_2629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2565])).
% 4.54/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.87  
% 4.54/1.87  Inference rules
% 4.54/1.87  ----------------------
% 4.54/1.87  #Ref     : 0
% 4.54/1.87  #Sup     : 524
% 4.54/1.87  #Fact    : 0
% 4.54/1.87  #Define  : 0
% 4.54/1.87  #Split   : 6
% 4.54/1.87  #Chain   : 0
% 4.54/1.87  #Close   : 0
% 4.54/1.87  
% 4.54/1.87  Ordering : KBO
% 4.54/1.87  
% 4.54/1.87  Simplification rules
% 4.54/1.87  ----------------------
% 4.54/1.87  #Subsume      : 233
% 4.54/1.87  #Demod        : 49
% 4.54/1.87  #Tautology    : 44
% 4.54/1.87  #SimpNegUnit  : 12
% 4.54/1.87  #BackRed      : 0
% 4.54/1.87  
% 4.54/1.87  #Partial instantiations: 0
% 4.54/1.87  #Strategies tried      : 1
% 4.54/1.87  
% 4.54/1.87  Timing (in seconds)
% 4.54/1.87  ----------------------
% 4.54/1.87  Preprocessing        : 0.30
% 4.54/1.88  Parsing              : 0.17
% 4.54/1.88  CNF conversion       : 0.02
% 4.54/1.88  Main loop            : 0.75
% 4.54/1.88  Inferencing          : 0.29
% 4.54/1.88  Reduction            : 0.17
% 4.54/1.88  Demodulation         : 0.11
% 4.54/1.88  BG Simplification    : 0.03
% 4.54/1.88  Subsumption          : 0.21
% 4.54/1.88  Abstraction          : 0.03
% 4.54/1.88  MUC search           : 0.00
% 4.54/1.88  Cooper               : 0.00
% 4.54/1.88  Total                : 1.08
% 4.54/1.88  Index Insertion      : 0.00
% 4.54/1.88  Index Deletion       : 0.00
% 4.54/1.88  Index Matching       : 0.00
% 4.54/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
