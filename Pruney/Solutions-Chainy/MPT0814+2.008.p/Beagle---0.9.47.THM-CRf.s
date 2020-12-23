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
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 117 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 233 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_55,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_50,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [A_37,A_6] :
      ( r1_tarski(A_37,A_6)
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_84,plain,(
    ! [A_41,A_42] :
      ( r1_tarski(A_41,A_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_70])).

tff(c_88,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_84])).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_6',B_46)
      | ~ r1_tarski('#skF_9',B_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [B_52,B_53] :
      ( r2_hidden('#skF_6',B_52)
      | ~ r1_tarski(B_53,B_52)
      | ~ r1_tarski('#skF_9',B_53) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_123,plain,
    ( r2_hidden('#skF_6',k2_zfmisc_1('#skF_7','#skF_8'))
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_121])).

tff(c_128,plain,(
    r2_hidden('#skF_6',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_123])).

tff(c_290,plain,(
    ! [A_100,B_101,C_102] :
      ( k4_tarski('#skF_4'(A_100,B_101,C_102),'#skF_5'(A_100,B_101,C_102)) = A_100
      | ~ r2_hidden(A_100,k2_zfmisc_1(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_16,C_18,B_17,D_19] :
      ( r2_hidden(A_16,C_18)
      | ~ r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1098,plain,(
    ! [C_217,D_216,C_213,B_214,A_215] :
      ( r2_hidden('#skF_4'(A_215,B_214,C_213),C_217)
      | ~ r2_hidden(A_215,k2_zfmisc_1(C_217,D_216))
      | ~ r2_hidden(A_215,k2_zfmisc_1(B_214,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_26])).

tff(c_1143,plain,(
    ! [B_218,C_219] :
      ( r2_hidden('#skF_4'('#skF_6',B_218,C_219),'#skF_7')
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(B_218,C_219)) ) ),
    inference(resolution,[status(thm)],[c_128,c_1098])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] :
      ( k4_tarski('#skF_4'(A_11,B_12,C_13),'#skF_5'(A_11,B_12,C_13)) = A_11
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_17,D_19,A_16,C_18] :
      ( r2_hidden(B_17,D_19)
      | ~ r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_616,plain,(
    ! [C_148,C_152,D_151,B_149,A_150] :
      ( r2_hidden('#skF_5'(A_150,B_149,C_148),D_151)
      | ~ r2_hidden(A_150,k2_zfmisc_1(C_152,D_151))
      | ~ r2_hidden(A_150,k2_zfmisc_1(B_149,C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_24])).

tff(c_653,plain,(
    ! [B_153,C_154] :
      ( r2_hidden('#skF_5'('#skF_6',B_153,C_154),'#skF_8')
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(B_153,C_154)) ) ),
    inference(resolution,[status(thm)],[c_128,c_616])).

tff(c_32,plain,(
    ! [F_26,E_25] :
      ( ~ r2_hidden(F_26,'#skF_8')
      | ~ r2_hidden(E_25,'#skF_7')
      | k4_tarski(E_25,F_26) != '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_677,plain,(
    ! [E_157,B_158,C_159] :
      ( ~ r2_hidden(E_157,'#skF_7')
      | k4_tarski(E_157,'#skF_5'('#skF_6',B_158,C_159)) != '#skF_6'
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(B_158,C_159)) ) ),
    inference(resolution,[status(thm)],[c_653,c_32])).

tff(c_681,plain,(
    ! [B_12,C_13] :
      ( ~ r2_hidden('#skF_4'('#skF_6',B_12,C_13),'#skF_7')
      | ~ r2_hidden('#skF_6',k2_zfmisc_1(B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_677])).

tff(c_1151,plain,(
    ! [B_218,C_219] : ~ r2_hidden('#skF_6',k2_zfmisc_1(B_218,C_219)) ),
    inference(resolution,[status(thm)],[c_1143,c_681])).

tff(c_1155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1151,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.64  
% 3.53/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.64  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.53/1.64  
% 3.53/1.64  %Foreground sorts:
% 3.53/1.64  
% 3.53/1.64  
% 3.53/1.64  %Background operators:
% 3.53/1.64  
% 3.53/1.64  
% 3.53/1.64  %Foreground operators:
% 3.53/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.53/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.53/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.53/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.53/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.64  
% 3.53/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.65  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 3.53/1.65  tff(f_55, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.53/1.65  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.53/1.65  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.53/1.65  tff(f_46, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.53/1.65  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.53/1.65  tff(c_50, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.65  tff(c_59, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_50, c_4])).
% 3.53/1.65  tff(c_36, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.65  tff(c_28, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.65  tff(c_62, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.53/1.65  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.65  tff(c_70, plain, (![A_37, A_6]: (r1_tarski(A_37, A_6) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_62, c_8])).
% 3.53/1.65  tff(c_84, plain, (![A_41, A_42]: (r1_tarski(A_41, A_42) | ~m1_subset_1(A_41, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_28, c_70])).
% 3.53/1.65  tff(c_88, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_84])).
% 3.53/1.65  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.65  tff(c_89, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.65  tff(c_102, plain, (![B_46]: (r2_hidden('#skF_6', B_46) | ~r1_tarski('#skF_9', B_46))), inference(resolution, [status(thm)], [c_34, c_89])).
% 3.53/1.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.65  tff(c_121, plain, (![B_52, B_53]: (r2_hidden('#skF_6', B_52) | ~r1_tarski(B_53, B_52) | ~r1_tarski('#skF_9', B_53))), inference(resolution, [status(thm)], [c_102, c_2])).
% 3.53/1.65  tff(c_123, plain, (r2_hidden('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8')) | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_88, c_121])).
% 3.53/1.65  tff(c_128, plain, (r2_hidden('#skF_6', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_123])).
% 3.53/1.65  tff(c_290, plain, (![A_100, B_101, C_102]: (k4_tarski('#skF_4'(A_100, B_101, C_102), '#skF_5'(A_100, B_101, C_102))=A_100 | ~r2_hidden(A_100, k2_zfmisc_1(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.53/1.65  tff(c_26, plain, (![A_16, C_18, B_17, D_19]: (r2_hidden(A_16, C_18) | ~r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.65  tff(c_1098, plain, (![C_217, D_216, C_213, B_214, A_215]: (r2_hidden('#skF_4'(A_215, B_214, C_213), C_217) | ~r2_hidden(A_215, k2_zfmisc_1(C_217, D_216)) | ~r2_hidden(A_215, k2_zfmisc_1(B_214, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_26])).
% 3.53/1.65  tff(c_1143, plain, (![B_218, C_219]: (r2_hidden('#skF_4'('#skF_6', B_218, C_219), '#skF_7') | ~r2_hidden('#skF_6', k2_zfmisc_1(B_218, C_219)))), inference(resolution, [status(thm)], [c_128, c_1098])).
% 3.53/1.65  tff(c_20, plain, (![A_11, B_12, C_13]: (k4_tarski('#skF_4'(A_11, B_12, C_13), '#skF_5'(A_11, B_12, C_13))=A_11 | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.53/1.65  tff(c_24, plain, (![B_17, D_19, A_16, C_18]: (r2_hidden(B_17, D_19) | ~r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.65  tff(c_616, plain, (![C_148, C_152, D_151, B_149, A_150]: (r2_hidden('#skF_5'(A_150, B_149, C_148), D_151) | ~r2_hidden(A_150, k2_zfmisc_1(C_152, D_151)) | ~r2_hidden(A_150, k2_zfmisc_1(B_149, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_24])).
% 3.53/1.65  tff(c_653, plain, (![B_153, C_154]: (r2_hidden('#skF_5'('#skF_6', B_153, C_154), '#skF_8') | ~r2_hidden('#skF_6', k2_zfmisc_1(B_153, C_154)))), inference(resolution, [status(thm)], [c_128, c_616])).
% 3.53/1.65  tff(c_32, plain, (![F_26, E_25]: (~r2_hidden(F_26, '#skF_8') | ~r2_hidden(E_25, '#skF_7') | k4_tarski(E_25, F_26)!='#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.65  tff(c_677, plain, (![E_157, B_158, C_159]: (~r2_hidden(E_157, '#skF_7') | k4_tarski(E_157, '#skF_5'('#skF_6', B_158, C_159))!='#skF_6' | ~r2_hidden('#skF_6', k2_zfmisc_1(B_158, C_159)))), inference(resolution, [status(thm)], [c_653, c_32])).
% 3.53/1.65  tff(c_681, plain, (![B_12, C_13]: (~r2_hidden('#skF_4'('#skF_6', B_12, C_13), '#skF_7') | ~r2_hidden('#skF_6', k2_zfmisc_1(B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_677])).
% 3.53/1.65  tff(c_1151, plain, (![B_218, C_219]: (~r2_hidden('#skF_6', k2_zfmisc_1(B_218, C_219)))), inference(resolution, [status(thm)], [c_1143, c_681])).
% 3.53/1.65  tff(c_1155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1151, c_128])).
% 3.53/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.65  
% 3.53/1.65  Inference rules
% 3.53/1.65  ----------------------
% 3.53/1.65  #Ref     : 0
% 3.53/1.65  #Sup     : 266
% 3.53/1.65  #Fact    : 0
% 3.53/1.65  #Define  : 0
% 3.53/1.65  #Split   : 16
% 3.53/1.65  #Chain   : 0
% 3.53/1.65  #Close   : 0
% 3.53/1.65  
% 3.53/1.65  Ordering : KBO
% 3.53/1.65  
% 3.53/1.65  Simplification rules
% 3.53/1.65  ----------------------
% 3.53/1.65  #Subsume      : 46
% 3.53/1.65  #Demod        : 11
% 3.53/1.65  #Tautology    : 16
% 3.53/1.65  #SimpNegUnit  : 6
% 3.53/1.65  #BackRed      : 1
% 3.53/1.65  
% 3.53/1.65  #Partial instantiations: 0
% 3.53/1.65  #Strategies tried      : 1
% 3.53/1.65  
% 3.53/1.65  Timing (in seconds)
% 3.53/1.65  ----------------------
% 3.53/1.65  Preprocessing        : 0.28
% 3.53/1.65  Parsing              : 0.15
% 3.53/1.65  CNF conversion       : 0.02
% 3.53/1.65  Main loop            : 0.52
% 3.53/1.65  Inferencing          : 0.18
% 3.53/1.65  Reduction            : 0.13
% 3.53/1.65  Demodulation         : 0.08
% 3.53/1.65  BG Simplification    : 0.02
% 3.53/1.65  Subsumption          : 0.14
% 3.53/1.65  Abstraction          : 0.02
% 3.53/1.65  MUC search           : 0.00
% 3.53/1.65  Cooper               : 0.00
% 3.53/1.65  Total                : 0.83
% 3.53/1.65  Index Insertion      : 0.00
% 3.53/1.65  Index Deletion       : 0.00
% 3.53/1.65  Index Matching       : 0.00
% 3.53/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
