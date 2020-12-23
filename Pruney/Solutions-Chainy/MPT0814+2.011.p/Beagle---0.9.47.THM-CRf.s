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
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 134 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 264 expanded)
%              Number of equality atoms :    8 (  21 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_49,axiom,(
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

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_17] : k3_tarski(k1_zfmisc_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k3_tarski(B_28))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_31,A_32] :
      ( r1_tarski(A_31,A_32)
      | ~ r2_hidden(A_31,k1_zfmisc_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_39])).

tff(c_48,plain,(
    ! [A_19,A_32] :
      ( r1_tarski(A_19,A_32)
      | v1_xboole_0(k1_zfmisc_1(A_32))
      | ~ m1_subset_1(A_19,k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_52,plain,(
    ! [A_33,A_34] :
      ( r1_tarski(A_33,A_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(A_34)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_48])).

tff(c_56,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_4',B_45)
      | ~ r1_tarski('#skF_7',B_45) ) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [B_51,B_52] :
      ( r2_hidden('#skF_4',B_51)
      | ~ r1_tarski(B_52,B_51)
      | ~ r1_tarski('#skF_7',B_52) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_117,plain,
    ( r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_113])).

tff(c_123,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_117])).

tff(c_224,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_tarski('#skF_2'(A_77,B_78,C_79),'#skF_3'(A_77,B_78,C_79)) = A_77
      | ~ r2_hidden(A_77,k2_zfmisc_1(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_394,plain,(
    ! [D_127,B_129,C_130,A_128,C_131] :
      ( r2_hidden('#skF_2'(A_128,B_129,C_130),C_131)
      | ~ r2_hidden(A_128,k2_zfmisc_1(C_131,D_127))
      | ~ r2_hidden(A_128,k2_zfmisc_1(B_129,C_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_417,plain,(
    ! [B_132,C_133] :
      ( r2_hidden('#skF_2'('#skF_4',B_132,C_133),'#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_123,c_394])).

tff(c_426,plain,(
    ! [B_132,C_133,B_2] :
      ( r2_hidden('#skF_2'('#skF_4',B_132,C_133),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_417,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_tarski('#skF_2'(A_6,B_7,C_8),'#skF_3'(A_6,B_7,C_8)) = A_6
      | ~ r2_hidden(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_534,plain,(
    ! [C_154,D_150,B_152,C_153,A_151] :
      ( r2_hidden('#skF_3'(A_151,B_152,C_153),D_150)
      | ~ r2_hidden(A_151,k2_zfmisc_1(C_154,D_150))
      | ~ r2_hidden(A_151,k2_zfmisc_1(B_152,C_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_14])).

tff(c_564,plain,(
    ! [B_155,C_156] :
      ( r2_hidden('#skF_3'('#skF_4',B_155,C_156),'#skF_6')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_155,C_156)) ) ),
    inference(resolution,[status(thm)],[c_123,c_534])).

tff(c_24,plain,(
    ! [F_24,E_23] :
      ( ~ r2_hidden(F_24,'#skF_6')
      | ~ r2_hidden(E_23,'#skF_5')
      | k4_tarski(E_23,F_24) != '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_625,plain,(
    ! [E_162,B_163,C_164] :
      ( ~ r2_hidden(E_162,'#skF_5')
      | k4_tarski(E_162,'#skF_3'('#skF_4',B_163,C_164)) != '#skF_4'
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_163,C_164)) ) ),
    inference(resolution,[status(thm)],[c_564,c_24])).

tff(c_630,plain,(
    ! [B_165,C_166] :
      ( ~ r2_hidden('#skF_2'('#skF_4',B_165,C_166),'#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_165,C_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_625])).

tff(c_634,plain,(
    ! [B_132,C_133] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden('#skF_4',k2_zfmisc_1(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_426,c_630])).

tff(c_643,plain,(
    ! [B_132,C_133] : ~ r2_hidden('#skF_4',k2_zfmisc_1(B_132,C_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_634])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:31:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.55  
% 3.16/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.56  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.16/1.56  
% 3.16/1.56  %Foreground sorts:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Background operators:
% 3.16/1.56  
% 3.16/1.56  
% 3.16/1.56  %Foreground operators:
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.16/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.56  
% 3.16/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.57  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 3.16/1.57  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.16/1.57  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.16/1.57  tff(f_51, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.16/1.57  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.16/1.57  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.16/1.57  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.16/1.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_72, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_81, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_72])).
% 3.16/1.57  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.57  tff(c_20, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.57  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.57  tff(c_18, plain, (![A_17]: (k3_tarski(k1_zfmisc_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.57  tff(c_39, plain, (![A_27, B_28]: (r1_tarski(A_27, k3_tarski(B_28)) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.57  tff(c_44, plain, (![A_31, A_32]: (r1_tarski(A_31, A_32) | ~r2_hidden(A_31, k1_zfmisc_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_39])).
% 3.16/1.57  tff(c_48, plain, (![A_19, A_32]: (r1_tarski(A_19, A_32) | v1_xboole_0(k1_zfmisc_1(A_32)) | ~m1_subset_1(A_19, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_22, c_44])).
% 3.16/1.57  tff(c_52, plain, (![A_33, A_34]: (r1_tarski(A_33, A_34) | ~m1_subset_1(A_33, k1_zfmisc_1(A_34)))), inference(negUnitSimplification, [status(thm)], [c_20, c_48])).
% 3.16/1.57  tff(c_56, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_52])).
% 3.16/1.57  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.57  tff(c_84, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_94, plain, (![B_45]: (r2_hidden('#skF_4', B_45) | ~r1_tarski('#skF_7', B_45))), inference(resolution, [status(thm)], [c_26, c_84])).
% 3.16/1.57  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_113, plain, (![B_51, B_52]: (r2_hidden('#skF_4', B_51) | ~r1_tarski(B_52, B_51) | ~r1_tarski('#skF_7', B_52))), inference(resolution, [status(thm)], [c_94, c_2])).
% 3.16/1.57  tff(c_117, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_113])).
% 3.16/1.57  tff(c_123, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_117])).
% 3.16/1.57  tff(c_224, plain, (![A_77, B_78, C_79]: (k4_tarski('#skF_2'(A_77, B_78, C_79), '#skF_3'(A_77, B_78, C_79))=A_77 | ~r2_hidden(A_77, k2_zfmisc_1(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.57  tff(c_16, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.57  tff(c_394, plain, (![D_127, B_129, C_130, A_128, C_131]: (r2_hidden('#skF_2'(A_128, B_129, C_130), C_131) | ~r2_hidden(A_128, k2_zfmisc_1(C_131, D_127)) | ~r2_hidden(A_128, k2_zfmisc_1(B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 3.16/1.57  tff(c_417, plain, (![B_132, C_133]: (r2_hidden('#skF_2'('#skF_4', B_132, C_133), '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_132, C_133)))), inference(resolution, [status(thm)], [c_123, c_394])).
% 3.16/1.57  tff(c_426, plain, (![B_132, C_133, B_2]: (r2_hidden('#skF_2'('#skF_4', B_132, C_133), B_2) | ~r1_tarski('#skF_5', B_2) | ~r2_hidden('#skF_4', k2_zfmisc_1(B_132, C_133)))), inference(resolution, [status(thm)], [c_417, c_2])).
% 3.16/1.57  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski('#skF_2'(A_6, B_7, C_8), '#skF_3'(A_6, B_7, C_8))=A_6 | ~r2_hidden(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.57  tff(c_14, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.57  tff(c_534, plain, (![C_154, D_150, B_152, C_153, A_151]: (r2_hidden('#skF_3'(A_151, B_152, C_153), D_150) | ~r2_hidden(A_151, k2_zfmisc_1(C_154, D_150)) | ~r2_hidden(A_151, k2_zfmisc_1(B_152, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_14])).
% 3.16/1.57  tff(c_564, plain, (![B_155, C_156]: (r2_hidden('#skF_3'('#skF_4', B_155, C_156), '#skF_6') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_155, C_156)))), inference(resolution, [status(thm)], [c_123, c_534])).
% 3.16/1.57  tff(c_24, plain, (![F_24, E_23]: (~r2_hidden(F_24, '#skF_6') | ~r2_hidden(E_23, '#skF_5') | k4_tarski(E_23, F_24)!='#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.57  tff(c_625, plain, (![E_162, B_163, C_164]: (~r2_hidden(E_162, '#skF_5') | k4_tarski(E_162, '#skF_3'('#skF_4', B_163, C_164))!='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1(B_163, C_164)))), inference(resolution, [status(thm)], [c_564, c_24])).
% 3.16/1.57  tff(c_630, plain, (![B_165, C_166]: (~r2_hidden('#skF_2'('#skF_4', B_165, C_166), '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_165, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_625])).
% 3.16/1.57  tff(c_634, plain, (![B_132, C_133]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden('#skF_4', k2_zfmisc_1(B_132, C_133)))), inference(resolution, [status(thm)], [c_426, c_630])).
% 3.16/1.57  tff(c_643, plain, (![B_132, C_133]: (~r2_hidden('#skF_4', k2_zfmisc_1(B_132, C_133)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_634])).
% 3.16/1.57  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_123])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 143
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 7
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 23
% 3.16/1.57  #Demod        : 16
% 3.16/1.57  #Tautology    : 16
% 3.16/1.57  #SimpNegUnit  : 10
% 3.16/1.57  #BackRed      : 1
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 0
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.31
% 3.16/1.57  Parsing              : 0.17
% 3.16/1.57  CNF conversion       : 0.02
% 3.16/1.57  Main loop            : 0.38
% 3.16/1.57  Inferencing          : 0.15
% 3.16/1.57  Reduction            : 0.10
% 3.16/1.57  Demodulation         : 0.06
% 3.16/1.58  BG Simplification    : 0.02
% 3.16/1.58  Subsumption          : 0.09
% 3.16/1.58  Abstraction          : 0.02
% 3.16/1.58  MUC search           : 0.00
% 3.16/1.58  Cooper               : 0.00
% 3.16/1.58  Total                : 0.73
% 3.16/1.58  Index Insertion      : 0.00
% 3.16/1.58  Index Deletion       : 0.00
% 3.16/1.58  Index Matching       : 0.00
% 3.16/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
