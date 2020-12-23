%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 105 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 213 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_26])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [C_30,B_31,A_32] :
      ( r2_hidden(C_30,B_31)
      | ~ r2_hidden(C_30,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [B_35] :
      ( r2_hidden('#skF_4',B_35)
      | ~ r1_tarski('#skF_7',B_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [B_36,B_37] :
      ( r2_hidden('#skF_4',B_36)
      | ~ r1_tarski(B_37,B_36)
      | ~ r1_tarski('#skF_7',B_37) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_67,plain,
    ( r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_71,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_67])).

tff(c_141,plain,(
    ! [A_63,B_64,C_65] :
      ( k4_tarski('#skF_2'(A_63,B_64,C_65),'#skF_3'(A_63,B_64,C_65)) = A_63
      | ~ r2_hidden(A_63,k2_zfmisc_1(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12,D_14] :
      ( r2_hidden(A_11,C_13)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [C_67,A_70,B_68,C_66,D_69] :
      ( r2_hidden('#skF_2'(A_70,B_68,C_67),C_66)
      | ~ r2_hidden(A_70,k2_zfmisc_1(C_66,D_69))
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_68,C_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_14])).

tff(c_181,plain,(
    ! [B_71,C_72] :
      ( r2_hidden('#skF_2'('#skF_4',B_71,C_72),'#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_71,C_72)) ) ),
    inference(resolution,[status(thm)],[c_71,c_159])).

tff(c_184,plain,(
    ! [B_71,C_72,B_2] :
      ( r2_hidden('#skF_2'('#skF_4',B_71,C_72),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_71,C_72)) ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_tarski('#skF_2'(A_6,B_7,C_8),'#skF_3'(A_6,B_7,C_8)) = A_6
      | ~ r2_hidden(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_12,D_14,A_11,C_13] :
      ( r2_hidden(B_12,D_14)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,(
    ! [C_80,C_79,B_81,A_83,D_82] :
      ( r2_hidden('#skF_3'(A_83,B_81,C_80),D_82)
      | ~ r2_hidden(A_83,k2_zfmisc_1(C_79,D_82))
      | ~ r2_hidden(A_83,k2_zfmisc_1(B_81,C_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_12])).

tff(c_225,plain,(
    ! [B_84,C_85] :
      ( r2_hidden('#skF_3'('#skF_4',B_84,C_85),'#skF_6')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_84,C_85)) ) ),
    inference(resolution,[status(thm)],[c_71,c_199])).

tff(c_20,plain,(
    ! [F_20,E_19] :
      ( ~ r2_hidden(F_20,'#skF_6')
      | ~ r2_hidden(E_19,'#skF_5')
      | k4_tarski(E_19,F_20) != '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_250,plain,(
    ! [E_89,B_90,C_91] :
      ( ~ r2_hidden(E_89,'#skF_5')
      | k4_tarski(E_89,'#skF_3'('#skF_4',B_90,C_91)) != '#skF_4'
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_90,C_91)) ) ),
    inference(resolution,[status(thm)],[c_225,c_20])).

tff(c_264,plain,(
    ! [B_97,C_98] :
      ( ~ r2_hidden('#skF_2'('#skF_4',B_97,C_98),'#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_97,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_268,plain,(
    ! [B_71,C_72] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_71,C_72)) ) ),
    inference(resolution,[status(thm)],[c_184,c_264])).

tff(c_274,plain,(
    ! [B_71,C_72] : ~ r2_hidden('#skF_4',k2_zfmisc_1(B_71,C_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_268])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.16/1.26  
% 2.16/1.26  %Foreground sorts:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Background operators:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Foreground operators:
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.16/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.26  
% 2.16/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.27  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.16/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.27  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.16/1.27  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.16/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_36, plain, (![A_27, B_28]: (~r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_41, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_36])).
% 2.16/1.27  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.27  tff(c_26, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.27  tff(c_34, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_26])).
% 2.16/1.27  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.27  tff(c_43, plain, (![C_30, B_31, A_32]: (r2_hidden(C_30, B_31) | ~r2_hidden(C_30, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_55, plain, (![B_35]: (r2_hidden('#skF_4', B_35) | ~r1_tarski('#skF_7', B_35))), inference(resolution, [status(thm)], [c_22, c_43])).
% 2.16/1.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_63, plain, (![B_36, B_37]: (r2_hidden('#skF_4', B_36) | ~r1_tarski(B_37, B_36) | ~r1_tarski('#skF_7', B_37))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.16/1.27  tff(c_67, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.16/1.27  tff(c_71, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_67])).
% 2.16/1.27  tff(c_141, plain, (![A_63, B_64, C_65]: (k4_tarski('#skF_2'(A_63, B_64, C_65), '#skF_3'(A_63, B_64, C_65))=A_63 | ~r2_hidden(A_63, k2_zfmisc_1(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.27  tff(c_14, plain, (![A_11, C_13, B_12, D_14]: (r2_hidden(A_11, C_13) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.27  tff(c_159, plain, (![C_67, A_70, B_68, C_66, D_69]: (r2_hidden('#skF_2'(A_70, B_68, C_67), C_66) | ~r2_hidden(A_70, k2_zfmisc_1(C_66, D_69)) | ~r2_hidden(A_70, k2_zfmisc_1(B_68, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_14])).
% 2.16/1.27  tff(c_181, plain, (![B_71, C_72]: (r2_hidden('#skF_2'('#skF_4', B_71, C_72), '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_71, C_72)))), inference(resolution, [status(thm)], [c_71, c_159])).
% 2.16/1.27  tff(c_184, plain, (![B_71, C_72, B_2]: (r2_hidden('#skF_2'('#skF_4', B_71, C_72), B_2) | ~r1_tarski('#skF_5', B_2) | ~r2_hidden('#skF_4', k2_zfmisc_1(B_71, C_72)))), inference(resolution, [status(thm)], [c_181, c_2])).
% 2.16/1.27  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski('#skF_2'(A_6, B_7, C_8), '#skF_3'(A_6, B_7, C_8))=A_6 | ~r2_hidden(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.27  tff(c_12, plain, (![B_12, D_14, A_11, C_13]: (r2_hidden(B_12, D_14) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.27  tff(c_199, plain, (![C_80, C_79, B_81, A_83, D_82]: (r2_hidden('#skF_3'(A_83, B_81, C_80), D_82) | ~r2_hidden(A_83, k2_zfmisc_1(C_79, D_82)) | ~r2_hidden(A_83, k2_zfmisc_1(B_81, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_12])).
% 2.16/1.27  tff(c_225, plain, (![B_84, C_85]: (r2_hidden('#skF_3'('#skF_4', B_84, C_85), '#skF_6') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_84, C_85)))), inference(resolution, [status(thm)], [c_71, c_199])).
% 2.16/1.27  tff(c_20, plain, (![F_20, E_19]: (~r2_hidden(F_20, '#skF_6') | ~r2_hidden(E_19, '#skF_5') | k4_tarski(E_19, F_20)!='#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.27  tff(c_250, plain, (![E_89, B_90, C_91]: (~r2_hidden(E_89, '#skF_5') | k4_tarski(E_89, '#skF_3'('#skF_4', B_90, C_91))!='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1(B_90, C_91)))), inference(resolution, [status(thm)], [c_225, c_20])).
% 2.16/1.27  tff(c_264, plain, (![B_97, C_98]: (~r2_hidden('#skF_2'('#skF_4', B_97, C_98), '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_97, C_98)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_250])).
% 2.16/1.27  tff(c_268, plain, (![B_71, C_72]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_71, C_72)))), inference(resolution, [status(thm)], [c_184, c_264])).
% 2.16/1.27  tff(c_274, plain, (![B_71, C_72]: (~r2_hidden('#skF_4', k2_zfmisc_1(B_71, C_72)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_268])).
% 2.16/1.27  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_71])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 58
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 2
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 9
% 2.16/1.27  #Demod        : 6
% 2.16/1.27  #Tautology    : 9
% 2.16/1.27  #SimpNegUnit  : 1
% 2.16/1.27  #BackRed      : 1
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.28  Preprocessing        : 0.27
% 2.16/1.28  Parsing              : 0.15
% 2.16/1.28  CNF conversion       : 0.02
% 2.16/1.28  Main loop            : 0.25
% 2.16/1.28  Inferencing          : 0.10
% 2.16/1.28  Reduction            : 0.06
% 2.16/1.28  Demodulation         : 0.04
% 2.16/1.28  BG Simplification    : 0.01
% 2.16/1.28  Subsumption          : 0.06
% 2.16/1.28  Abstraction          : 0.01
% 2.16/1.28  MUC search           : 0.00
% 2.16/1.28  Cooper               : 0.00
% 2.16/1.28  Total                : 0.54
% 2.16/1.28  Index Insertion      : 0.00
% 2.16/1.28  Index Deletion       : 0.00
% 2.16/1.28  Index Matching       : 0.00
% 2.16/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
