%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:07 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 237 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_123,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_57,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_4'(A_31,B_32),A_31)
      | r1_tarski(B_32,k1_setfam_1(A_31))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_34,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_3'(A_24,B_25),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_349,plain,(
    ! [A_106,B_107,B_108] :
      ( r2_hidden('#skF_3'(A_106,B_107),B_108)
      | ~ r1_tarski(B_107,B_108)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_959,plain,(
    ! [A_199,B_200,B_201,B_202] :
      ( r2_hidden('#skF_3'(A_199,B_200),B_201)
      | ~ r1_tarski(B_202,B_201)
      | ~ r1_tarski(B_200,B_202)
      | ~ r2_hidden(A_199,B_200) ) ),
    inference(resolution,[status(thm)],[c_349,c_2])).

tff(c_969,plain,(
    ! [A_203,B_204] :
      ( r2_hidden('#skF_3'(A_203,B_204),'#skF_6')
      | ~ r1_tarski(B_204,'#skF_5')
      | ~ r2_hidden(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_32,c_959])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( v3_ordinal1(A_34)
      | ~ r2_hidden(A_34,B_35)
      | ~ v3_ordinal1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_982,plain,(
    ! [A_203,B_204] :
      ( v3_ordinal1('#skF_3'(A_203,B_204))
      | ~ v3_ordinal1('#skF_6')
      | ~ r1_tarski(B_204,'#skF_5')
      | ~ r2_hidden(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_969,c_24])).

tff(c_991,plain,(
    ! [A_203,B_204] :
      ( v3_ordinal1('#skF_3'(A_203,B_204))
      | ~ r1_tarski(B_204,'#skF_5')
      | ~ r2_hidden(A_203,B_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_982])).

tff(c_81,plain,(
    ! [A_24,B_25,B_62] :
      ( r2_hidden('#skF_3'(A_24,B_25),B_62)
      | ~ r1_tarski(B_25,B_62)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_40,plain,(
    ! [C_45] :
      ( v3_ordinal1('#skF_7'(C_45))
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ v3_ordinal1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ! [C_45] :
      ( r2_hidden('#skF_7'(C_45),'#skF_5')
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ v3_ordinal1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26,plain,(
    ! [B_38,A_36] :
      ( r2_hidden(B_38,A_36)
      | r1_ordinal1(A_36,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_249,plain,(
    ! [D_93,A_94,B_95] :
      ( ~ r2_hidden(D_93,'#skF_3'(A_94,B_95))
      | ~ r2_hidden(D_93,B_95)
      | ~ r2_hidden(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1192,plain,(
    ! [B_229,B_230,A_231] :
      ( ~ r2_hidden(B_229,B_230)
      | ~ r2_hidden(A_231,B_230)
      | r1_ordinal1('#skF_3'(A_231,B_230),B_229)
      | ~ v3_ordinal1(B_229)
      | ~ v3_ordinal1('#skF_3'(A_231,B_230)) ) ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_36,plain,(
    ! [C_45] :
      ( ~ r1_ordinal1(C_45,'#skF_7'(C_45))
      | ~ r2_hidden(C_45,'#skF_5')
      | ~ v3_ordinal1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1651,plain,(
    ! [A_260,B_261] :
      ( ~ r2_hidden('#skF_3'(A_260,B_261),'#skF_5')
      | ~ r2_hidden('#skF_7'('#skF_3'(A_260,B_261)),B_261)
      | ~ r2_hidden(A_260,B_261)
      | ~ v3_ordinal1('#skF_7'('#skF_3'(A_260,B_261)))
      | ~ v3_ordinal1('#skF_3'(A_260,B_261)) ) ),
    inference(resolution,[status(thm)],[c_1192,c_36])).

tff(c_1897,plain,(
    ! [A_286] :
      ( ~ r2_hidden(A_286,'#skF_5')
      | ~ v3_ordinal1('#skF_7'('#skF_3'(A_286,'#skF_5')))
      | ~ r2_hidden('#skF_3'(A_286,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_3'(A_286,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1651])).

tff(c_1902,plain,(
    ! [A_287] :
      ( ~ r2_hidden(A_287,'#skF_5')
      | ~ r2_hidden('#skF_3'(A_287,'#skF_5'),'#skF_5')
      | ~ v3_ordinal1('#skF_3'(A_287,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1897])).

tff(c_1910,plain,(
    ! [A_24] :
      ( ~ v3_ordinal1('#skF_3'(A_24,'#skF_5'))
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_24,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_81,c_1902])).

tff(c_1926,plain,(
    ! [A_288] :
      ( ~ v3_ordinal1('#skF_3'(A_288,'#skF_5'))
      | ~ r2_hidden(A_288,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1910])).

tff(c_1930,plain,(
    ! [A_203] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_203,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_991,c_1926])).

tff(c_1944,plain,(
    ! [A_289] : ~ r2_hidden(A_289,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1930])).

tff(c_1968,plain,(
    ! [B_32] :
      ( r1_tarski(B_32,k1_setfam_1('#skF_5'))
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_22,c_1944])).

tff(c_2061,plain,(
    ! [B_294] : r1_tarski(B_294,k1_setfam_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1968])).

tff(c_14,plain,(
    ! [A_6] : r2_hidden(A_6,'#skF_2'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_6,B_62] :
      ( r2_hidden(A_6,B_62)
      | ~ r1_tarski('#skF_2'(A_6),B_62) ) ),
    inference(resolution,[status(thm)],[c_14,c_71])).

tff(c_2106,plain,(
    ! [A_295] : r2_hidden(A_295,k1_setfam_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2061,c_83])).

tff(c_99,plain,(
    ! [C_67,A_68,B_69] :
      ( ~ r2_hidden(C_67,A_68)
      | ~ r2_hidden(B_69,C_67)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_115,plain,(
    ! [B_70,A_71] :
      ( ~ r2_hidden(B_70,A_71)
      | ~ r2_hidden('#skF_2'(A_71),B_70) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_120,plain,(
    ! [A_71] : ~ r2_hidden('#skF_2'('#skF_2'(A_71)),A_71) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_2153,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2106,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:26:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.82  
% 4.53/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.82  %$ r2_tarski > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 4.53/1.82  
% 4.53/1.82  %Foreground sorts:
% 4.53/1.82  
% 4.53/1.82  
% 4.53/1.82  %Background operators:
% 4.53/1.82  
% 4.53/1.82  
% 4.53/1.82  %Foreground operators:
% 4.53/1.82  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.53/1.82  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 4.53/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.53/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.82  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.53/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.53/1.82  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.53/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.53/1.82  
% 4.69/1.83  tff(f_123, negated_conjecture, ~(![A, B]: (v3_ordinal1(B) => ~((r1_tarski(A, B) & ~(A = k1_xboole_0)) & (![C]: (v3_ordinal1(C) => ~(r2_hidden(C, A) & (![D]: (v3_ordinal1(D) => (r2_hidden(D, A) => r1_ordinal1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 4.69/1.83  tff(f_79, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 4.69/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.69/1.83  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.69/1.83  tff(f_85, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.69/1.83  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.69/1.83  tff(f_57, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 4.69/1.83  tff(f_101, axiom, (![A, B, C]: ~((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 4.69/1.83  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.83  tff(c_22, plain, (![A_31, B_32]: (r2_hidden('#skF_4'(A_31, B_32), A_31) | r1_tarski(B_32, k1_setfam_1(A_31)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.83  tff(c_49, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.84  tff(c_57, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(resolution, [status(thm)], [c_49, c_4])).
% 4.69/1.84  tff(c_34, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.84  tff(c_32, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.84  tff(c_18, plain, (![A_24, B_25]: (r2_hidden('#skF_3'(A_24, B_25), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.69/1.84  tff(c_71, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.84  tff(c_349, plain, (![A_106, B_107, B_108]: (r2_hidden('#skF_3'(A_106, B_107), B_108) | ~r1_tarski(B_107, B_108) | ~r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_18, c_71])).
% 4.69/1.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.84  tff(c_959, plain, (![A_199, B_200, B_201, B_202]: (r2_hidden('#skF_3'(A_199, B_200), B_201) | ~r1_tarski(B_202, B_201) | ~r1_tarski(B_200, B_202) | ~r2_hidden(A_199, B_200))), inference(resolution, [status(thm)], [c_349, c_2])).
% 4.69/1.84  tff(c_969, plain, (![A_203, B_204]: (r2_hidden('#skF_3'(A_203, B_204), '#skF_6') | ~r1_tarski(B_204, '#skF_5') | ~r2_hidden(A_203, B_204))), inference(resolution, [status(thm)], [c_32, c_959])).
% 4.69/1.84  tff(c_24, plain, (![A_34, B_35]: (v3_ordinal1(A_34) | ~r2_hidden(A_34, B_35) | ~v3_ordinal1(B_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.69/1.84  tff(c_982, plain, (![A_203, B_204]: (v3_ordinal1('#skF_3'(A_203, B_204)) | ~v3_ordinal1('#skF_6') | ~r1_tarski(B_204, '#skF_5') | ~r2_hidden(A_203, B_204))), inference(resolution, [status(thm)], [c_969, c_24])).
% 4.69/1.84  tff(c_991, plain, (![A_203, B_204]: (v3_ordinal1('#skF_3'(A_203, B_204)) | ~r1_tarski(B_204, '#skF_5') | ~r2_hidden(A_203, B_204))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_982])).
% 4.69/1.84  tff(c_81, plain, (![A_24, B_25, B_62]: (r2_hidden('#skF_3'(A_24, B_25), B_62) | ~r1_tarski(B_25, B_62) | ~r2_hidden(A_24, B_25))), inference(resolution, [status(thm)], [c_18, c_71])).
% 4.69/1.84  tff(c_40, plain, (![C_45]: (v3_ordinal1('#skF_7'(C_45)) | ~r2_hidden(C_45, '#skF_5') | ~v3_ordinal1(C_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.84  tff(c_38, plain, (![C_45]: (r2_hidden('#skF_7'(C_45), '#skF_5') | ~r2_hidden(C_45, '#skF_5') | ~v3_ordinal1(C_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.84  tff(c_26, plain, (![B_38, A_36]: (r2_hidden(B_38, A_36) | r1_ordinal1(A_36, B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.69/1.84  tff(c_249, plain, (![D_93, A_94, B_95]: (~r2_hidden(D_93, '#skF_3'(A_94, B_95)) | ~r2_hidden(D_93, B_95) | ~r2_hidden(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.69/1.84  tff(c_1192, plain, (![B_229, B_230, A_231]: (~r2_hidden(B_229, B_230) | ~r2_hidden(A_231, B_230) | r1_ordinal1('#skF_3'(A_231, B_230), B_229) | ~v3_ordinal1(B_229) | ~v3_ordinal1('#skF_3'(A_231, B_230)))), inference(resolution, [status(thm)], [c_26, c_249])).
% 4.69/1.84  tff(c_36, plain, (![C_45]: (~r1_ordinal1(C_45, '#skF_7'(C_45)) | ~r2_hidden(C_45, '#skF_5') | ~v3_ordinal1(C_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/1.84  tff(c_1651, plain, (![A_260, B_261]: (~r2_hidden('#skF_3'(A_260, B_261), '#skF_5') | ~r2_hidden('#skF_7'('#skF_3'(A_260, B_261)), B_261) | ~r2_hidden(A_260, B_261) | ~v3_ordinal1('#skF_7'('#skF_3'(A_260, B_261))) | ~v3_ordinal1('#skF_3'(A_260, B_261)))), inference(resolution, [status(thm)], [c_1192, c_36])).
% 4.69/1.84  tff(c_1897, plain, (![A_286]: (~r2_hidden(A_286, '#skF_5') | ~v3_ordinal1('#skF_7'('#skF_3'(A_286, '#skF_5'))) | ~r2_hidden('#skF_3'(A_286, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_3'(A_286, '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_1651])).
% 4.69/1.84  tff(c_1902, plain, (![A_287]: (~r2_hidden(A_287, '#skF_5') | ~r2_hidden('#skF_3'(A_287, '#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_3'(A_287, '#skF_5')))), inference(resolution, [status(thm)], [c_40, c_1897])).
% 4.69/1.84  tff(c_1910, plain, (![A_24]: (~v3_ordinal1('#skF_3'(A_24, '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_24, '#skF_5'))), inference(resolution, [status(thm)], [c_81, c_1902])).
% 4.69/1.84  tff(c_1926, plain, (![A_288]: (~v3_ordinal1('#skF_3'(A_288, '#skF_5')) | ~r2_hidden(A_288, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1910])).
% 4.69/1.84  tff(c_1930, plain, (![A_203]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_203, '#skF_5'))), inference(resolution, [status(thm)], [c_991, c_1926])).
% 4.69/1.84  tff(c_1944, plain, (![A_289]: (~r2_hidden(A_289, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1930])).
% 4.69/1.84  tff(c_1968, plain, (![B_32]: (r1_tarski(B_32, k1_setfam_1('#skF_5')) | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_22, c_1944])).
% 4.69/1.84  tff(c_2061, plain, (![B_294]: (r1_tarski(B_294, k1_setfam_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_30, c_1968])).
% 4.69/1.84  tff(c_14, plain, (![A_6]: (r2_hidden(A_6, '#skF_2'(A_6)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.69/1.84  tff(c_83, plain, (![A_6, B_62]: (r2_hidden(A_6, B_62) | ~r1_tarski('#skF_2'(A_6), B_62))), inference(resolution, [status(thm)], [c_14, c_71])).
% 4.69/1.84  tff(c_2106, plain, (![A_295]: (r2_hidden(A_295, k1_setfam_1('#skF_5')))), inference(resolution, [status(thm)], [c_2061, c_83])).
% 4.69/1.84  tff(c_99, plain, (![C_67, A_68, B_69]: (~r2_hidden(C_67, A_68) | ~r2_hidden(B_69, C_67) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.69/1.84  tff(c_115, plain, (![B_70, A_71]: (~r2_hidden(B_70, A_71) | ~r2_hidden('#skF_2'(A_71), B_70))), inference(resolution, [status(thm)], [c_14, c_99])).
% 4.69/1.84  tff(c_120, plain, (![A_71]: (~r2_hidden('#skF_2'('#skF_2'(A_71)), A_71))), inference(resolution, [status(thm)], [c_14, c_115])).
% 4.69/1.84  tff(c_2153, plain, $false, inference(resolution, [status(thm)], [c_2106, c_120])).
% 4.69/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.84  
% 4.69/1.84  Inference rules
% 4.69/1.84  ----------------------
% 4.69/1.84  #Ref     : 0
% 4.69/1.84  #Sup     : 465
% 4.69/1.84  #Fact    : 0
% 4.69/1.84  #Define  : 0
% 4.69/1.84  #Split   : 2
% 4.69/1.84  #Chain   : 0
% 4.69/1.84  #Close   : 0
% 4.69/1.84  
% 4.69/1.84  Ordering : KBO
% 4.69/1.84  
% 4.69/1.84  Simplification rules
% 4.69/1.84  ----------------------
% 4.69/1.84  #Subsume      : 61
% 4.69/1.84  #Demod        : 28
% 4.69/1.84  #Tautology    : 12
% 4.69/1.84  #SimpNegUnit  : 2
% 4.69/1.84  #BackRed      : 0
% 4.69/1.84  
% 4.69/1.84  #Partial instantiations: 0
% 4.69/1.84  #Strategies tried      : 1
% 4.69/1.84  
% 4.69/1.84  Timing (in seconds)
% 4.69/1.84  ----------------------
% 4.76/1.84  Preprocessing        : 0.32
% 4.76/1.84  Parsing              : 0.17
% 4.76/1.84  CNF conversion       : 0.02
% 4.76/1.84  Main loop            : 0.76
% 4.76/1.84  Inferencing          : 0.26
% 4.76/1.84  Reduction            : 0.19
% 4.76/1.84  Demodulation         : 0.11
% 4.76/1.84  BG Simplification    : 0.03
% 4.76/1.84  Subsumption          : 0.22
% 4.76/1.84  Abstraction          : 0.03
% 4.76/1.84  MUC search           : 0.00
% 4.76/1.84  Cooper               : 0.00
% 4.76/1.84  Total                : 1.12
% 4.76/1.84  Index Insertion      : 0.00
% 4.76/1.84  Index Deletion       : 0.00
% 4.76/1.84  Index Matching       : 0.00
% 4.76/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
