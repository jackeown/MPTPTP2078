%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 220 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  101 ( 451 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > np__0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(np__0,type,(
    np__0: $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    v1_xboole_0(np__0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc0_boole)).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_61,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_2'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_111,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [C_25,A_26] :
      ( r1_tarski(C_25,A_26)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_26] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_26)),A_26)
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_113,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45),B_46)
      | ~ r1_tarski(A_45,B_46)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | ~ r1_tarski(A_48,B_47)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_168,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(A_49)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_49)))
      | v1_xboole_0(k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_80,c_151])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_173,plain,(
    ! [A_50] :
      ( '#skF_1'(k1_zfmisc_1(A_50)) = k1_xboole_0
      | ~ v1_xboole_0(A_50)
      | v1_xboole_0(k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_81,plain,(
    ! [C_27,A_28] :
      ( r2_hidden(C_27,k1_zfmisc_1(A_28))
      | ~ r1_tarski(C_27,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_28,C_27] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ r1_tarski(C_27,A_28) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_181,plain,(
    ! [C_51,A_52] :
      ( ~ r1_tarski(C_51,A_52)
      | '#skF_1'(k1_zfmisc_1(A_52)) = k1_xboole_0
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_173,c_89])).

tff(c_214,plain,(
    ! [A_55] :
      ( '#skF_1'(k1_zfmisc_1(A_55)) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_111,c_181])).

tff(c_236,plain,(
    ! [A_56] :
      ( r1_tarski(k1_xboole_0,A_56)
      | v1_xboole_0(k1_zfmisc_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_80])).

tff(c_255,plain,(
    ! [C_60,A_61] :
      ( ~ r1_tarski(C_60,A_61)
      | r1_tarski(k1_xboole_0,A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_236,c_89])).

tff(c_272,plain,(
    ! [A_5] :
      ( r1_tarski(k1_xboole_0,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_111,c_255])).

tff(c_338,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_2'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_356,plain,(
    ! [B_82,A_83,B_84] :
      ( ~ v1_xboole_0(B_82)
      | ~ r1_tarski(A_83,B_82)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_378,plain,(
    ! [B_84,A_5] :
      ( r1_tarski(k1_xboole_0,B_84)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_272,c_356])).

tff(c_394,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_28,plain,(
    v1_xboole_0(np__0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    np__0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_28])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_50])).

tff(c_406,plain,(
    ! [B_84] : r1_tarski(k1_xboole_0,B_84) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_35,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32])).

tff(c_125,plain,(
    ! [A_42] :
      ( k3_yellow_0(k2_yellow_1(A_42)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_384,plain,(
    ! [A_85] :
      ( k3_yellow_0(k3_yellow_1(A_85)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_85))
      | v1_xboole_0(k1_zfmisc_1(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_125])).

tff(c_393,plain,(
    ! [A_11] :
      ( k3_yellow_0(k3_yellow_1(A_11)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(k1_xboole_0,A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_384])).

tff(c_420,plain,(
    ! [A_87] :
      ( k3_yellow_0(k3_yellow_1(A_87)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_87)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_393])).

tff(c_428,plain,(
    ! [C_88,A_89] :
      ( ~ r1_tarski(C_88,A_89)
      | k3_yellow_0(k3_yellow_1(A_89)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_420,c_89])).

tff(c_447,plain,(
    ! [B_84] : k3_yellow_0(k3_yellow_1(B_84)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_406,c_428])).

tff(c_34,plain,(
    k3_yellow_0(k3_yellow_1('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > np__0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.30  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.30  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.16/1.30  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.30  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.16/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.30  tff(np__0, type, np__0: $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.16/1.30  
% 2.16/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.31  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.16/1.31  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.31  tff(f_52, axiom, v1_xboole_0(np__0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', spc0_boole)).
% 2.16/1.31  tff(f_51, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.16/1.31  tff(f_61, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.16/1.31  tff(f_59, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 2.16/1.31  tff(f_64, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 2.16/1.31  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.31  tff(c_102, plain, (![A_35, B_36]: (~r2_hidden('#skF_2'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.31  tff(c_111, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.16/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.31  tff(c_75, plain, (![C_25, A_26]: (r1_tarski(C_25, A_26) | ~r2_hidden(C_25, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.31  tff(c_80, plain, (![A_26]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_26)), A_26) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_4, c_75])).
% 2.16/1.31  tff(c_113, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.31  tff(c_138, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45), B_46) | ~r1_tarski(A_45, B_46) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_4, c_113])).
% 2.16/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.31  tff(c_151, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | ~r1_tarski(A_48, B_47) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_138, c_2])).
% 2.16/1.31  tff(c_168, plain, (![A_49]: (~v1_xboole_0(A_49) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_49))) | v1_xboole_0(k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_80, c_151])).
% 2.16/1.31  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.31  tff(c_173, plain, (![A_50]: ('#skF_1'(k1_zfmisc_1(A_50))=k1_xboole_0 | ~v1_xboole_0(A_50) | v1_xboole_0(k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_168, c_12])).
% 2.16/1.31  tff(c_81, plain, (![C_27, A_28]: (r2_hidden(C_27, k1_zfmisc_1(A_28)) | ~r1_tarski(C_27, A_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.31  tff(c_89, plain, (![A_28, C_27]: (~v1_xboole_0(k1_zfmisc_1(A_28)) | ~r1_tarski(C_27, A_28))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.16/1.31  tff(c_181, plain, (![C_51, A_52]: (~r1_tarski(C_51, A_52) | '#skF_1'(k1_zfmisc_1(A_52))=k1_xboole_0 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_173, c_89])).
% 2.16/1.31  tff(c_214, plain, (![A_55]: ('#skF_1'(k1_zfmisc_1(A_55))=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_111, c_181])).
% 2.16/1.31  tff(c_236, plain, (![A_56]: (r1_tarski(k1_xboole_0, A_56) | v1_xboole_0(k1_zfmisc_1(A_56)) | ~v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_214, c_80])).
% 2.16/1.31  tff(c_255, plain, (![C_60, A_61]: (~r1_tarski(C_60, A_61) | r1_tarski(k1_xboole_0, A_61) | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_236, c_89])).
% 2.16/1.31  tff(c_272, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_111, c_255])).
% 2.16/1.31  tff(c_338, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_2'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.16/1.31  tff(c_356, plain, (![B_82, A_83, B_84]: (~v1_xboole_0(B_82) | ~r1_tarski(A_83, B_82) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_338, c_2])).
% 2.16/1.31  tff(c_378, plain, (![B_84, A_5]: (r1_tarski(k1_xboole_0, B_84) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_272, c_356])).
% 2.16/1.31  tff(c_394, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitLeft, [status(thm)], [c_378])).
% 2.16/1.31  tff(c_28, plain, (v1_xboole_0(np__0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.31  tff(c_45, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.31  tff(c_49, plain, (np__0=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.16/1.31  tff(c_50, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_49, c_28])).
% 2.16/1.31  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_50])).
% 2.16/1.31  tff(c_406, plain, (![B_84]: (r1_tarski(k1_xboole_0, B_84))), inference(splitRight, [status(thm)], [c_378])).
% 2.16/1.31  tff(c_16, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.31  tff(c_26, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.31  tff(c_32, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.31  tff(c_35, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32])).
% 2.16/1.31  tff(c_125, plain, (![A_42]: (k3_yellow_0(k2_yellow_1(A_42))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.31  tff(c_384, plain, (![A_85]: (k3_yellow_0(k3_yellow_1(A_85))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_85)) | v1_xboole_0(k1_zfmisc_1(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_125])).
% 2.16/1.31  tff(c_393, plain, (![A_11]: (k3_yellow_0(k3_yellow_1(A_11))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_16, c_384])).
% 2.16/1.31  tff(c_420, plain, (![A_87]: (k3_yellow_0(k3_yellow_1(A_87))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_393])).
% 2.16/1.31  tff(c_428, plain, (![C_88, A_89]: (~r1_tarski(C_88, A_89) | k3_yellow_0(k3_yellow_1(A_89))=k1_xboole_0)), inference(resolution, [status(thm)], [c_420, c_89])).
% 2.16/1.31  tff(c_447, plain, (![B_84]: (k3_yellow_0(k3_yellow_1(B_84))=k1_xboole_0)), inference(resolution, [status(thm)], [c_406, c_428])).
% 2.16/1.31  tff(c_34, plain, (k3_yellow_0(k3_yellow_1('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.31  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_34])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 98
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 1
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 33
% 2.16/1.31  #Demod        : 13
% 2.16/1.31  #Tautology    : 26
% 2.16/1.31  #SimpNegUnit  : 10
% 2.16/1.31  #BackRed      : 9
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.29
% 2.16/1.31  Parsing              : 0.15
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.26
% 2.16/1.31  Inferencing          : 0.10
% 2.16/1.31  Reduction            : 0.07
% 2.16/1.31  Demodulation         : 0.04
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.06
% 2.16/1.31  Abstraction          : 0.02
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.58
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
