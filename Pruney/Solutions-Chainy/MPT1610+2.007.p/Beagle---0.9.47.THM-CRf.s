%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 252 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  109 ( 516 expanded)
%              Number of equality atoms :   25 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xxreal_0 > v1_xreal_0 > v1_xcmplx_0 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_xreal_0,type,(
    v1_xreal_0: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v1_xcmplx_0,type,(
    v1_xcmplx_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xxreal_0,type,(
    v1_xxreal_0: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_59,axiom,(
    ? [A] :
      ( v1_xboole_0(A)
      & v1_xcmplx_0(A)
      & v1_xxreal_0(A)
      & v1_xreal_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_xreal_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_68,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_2'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [C_30,A_31] :
      ( r1_tarski(C_30,A_31)
      | ~ r2_hidden(C_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_31] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_31)),A_31)
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_4,c_89])).

tff(c_121,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44),B_45)
      | ~ r1_tarski(A_44,B_45)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_47,B_46)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_177,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(A_50)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_50)))
      | v1_xboole_0(k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_98,c_159])).

tff(c_34,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_12])).

tff(c_182,plain,(
    ! [A_51] :
      ( '#skF_1'(k1_zfmisc_1(A_51)) = '#skF_5'
      | ~ v1_xboole_0(A_51)
      | v1_xboole_0(k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_177,c_56])).

tff(c_83,plain,(
    ! [C_26,A_27] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [A_27,C_26] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_190,plain,(
    ! [C_52,A_53] :
      ( ~ r1_tarski(C_52,A_53)
      | '#skF_1'(k1_zfmisc_1(A_53)) = '#skF_5'
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_182,c_87])).

tff(c_206,plain,(
    ! [A_56] :
      ( '#skF_1'(k1_zfmisc_1(A_56)) = '#skF_5'
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_119,c_190])).

tff(c_228,plain,(
    ! [A_57] :
      ( r1_tarski('#skF_5',A_57)
      | v1_xboole_0(k1_zfmisc_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_98])).

tff(c_236,plain,(
    ! [C_58,A_59] :
      ( ~ r1_tarski(C_58,A_59)
      | r1_tarski('#skF_5',A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_228,c_87])).

tff(c_244,plain,(
    ! [A_5] :
      ( r1_tarski('#skF_5',A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_119,c_236])).

tff(c_326,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_2'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_344,plain,(
    ! [B_82,A_83,B_84] :
      ( ~ v1_xboole_0(B_82)
      | ~ r1_tarski(A_83,B_82)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_326,c_2])).

tff(c_368,plain,(
    ! [B_84,A_5] :
      ( r1_tarski('#skF_5',B_84)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_244,c_344])).

tff(c_385,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_34])).

tff(c_396,plain,(
    ! [B_84] : r1_tarski('#skF_5',B_84) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38])).

tff(c_36,plain,(
    ! [A_17] :
      ( k3_yellow_0(k2_yellow_1(A_17)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    ! [A_43] :
      ( k3_yellow_0(k2_yellow_1(A_43)) = '#skF_5'
      | ~ r2_hidden('#skF_5',A_43)
      | v1_xboole_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_36])).

tff(c_420,plain,(
    ! [A_91] :
      ( k3_yellow_0(k3_yellow_1(A_91)) = '#skF_5'
      | ~ r2_hidden('#skF_5',k1_zfmisc_1(A_91))
      | v1_xboole_0(k1_zfmisc_1(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_134])).

tff(c_427,plain,(
    ! [A_11] :
      ( k3_yellow_0(k3_yellow_1(A_11)) = '#skF_5'
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski('#skF_5',A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_420])).

tff(c_447,plain,(
    ! [A_94] :
      ( k3_yellow_0(k3_yellow_1(A_94)) = '#skF_5'
      | v1_xboole_0(k1_zfmisc_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_427])).

tff(c_455,plain,(
    ! [C_95,A_96] :
      ( ~ r1_tarski(C_95,A_96)
      | k3_yellow_0(k3_yellow_1(A_96)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_447,c_87])).

tff(c_485,plain,(
    ! [B_84] : k3_yellow_0(k3_yellow_1(B_84)) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_396,c_455])).

tff(c_40,plain,(
    k3_yellow_0(k3_yellow_1('#skF_6')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    k3_yellow_0(k3_yellow_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_40])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  %$ r2_hidden > r1_tarski > v1_xxreal_0 > v1_xreal_0 > v1_xcmplx_0 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.33  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.38/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.33  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.38/1.33  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.38/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.38/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.33  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.38/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.33  tff(v1_xreal_0, type, v1_xreal_0: $i > $o).
% 2.38/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.33  tff(v1_xcmplx_0, type, v1_xcmplx_0: $i > $o).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.33  tff(v1_xxreal_0, type, v1_xxreal_0: $i > $o).
% 2.38/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.38/1.33  
% 2.38/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.38/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/1.35  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.38/1.35  tff(f_59, axiom, (?[A]: (((v1_xboole_0(A) & v1_xcmplx_0(A)) & v1_xxreal_0(A)) & v1_xreal_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_xreal_0)).
% 2.38/1.35  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.38/1.35  tff(f_51, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.38/1.35  tff(f_68, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.38/1.35  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 2.38/1.35  tff(f_71, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 2.38/1.35  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.35  tff(c_110, plain, (![A_36, B_37]: (~r2_hidden('#skF_2'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.35  tff(c_119, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_110])).
% 2.38/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.35  tff(c_89, plain, (![C_30, A_31]: (r1_tarski(C_30, A_31) | ~r2_hidden(C_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.35  tff(c_98, plain, (![A_31]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_31)), A_31) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_4, c_89])).
% 2.38/1.35  tff(c_121, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.35  tff(c_146, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44), B_45) | ~r1_tarski(A_44, B_45) | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.38/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.35  tff(c_159, plain, (![B_46, A_47]: (~v1_xboole_0(B_46) | ~r1_tarski(A_47, B_46) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_146, c_2])).
% 2.38/1.35  tff(c_177, plain, (![A_50]: (~v1_xboole_0(A_50) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_50))) | v1_xboole_0(k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_98, c_159])).
% 2.38/1.35  tff(c_34, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.38/1.35  tff(c_51, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.35  tff(c_55, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.38/1.35  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.35  tff(c_56, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_12])).
% 2.38/1.35  tff(c_182, plain, (![A_51]: ('#skF_1'(k1_zfmisc_1(A_51))='#skF_5' | ~v1_xboole_0(A_51) | v1_xboole_0(k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_177, c_56])).
% 2.38/1.35  tff(c_83, plain, (![C_26, A_27]: (r2_hidden(C_26, k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.35  tff(c_87, plain, (![A_27, C_26]: (~v1_xboole_0(k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.38/1.35  tff(c_190, plain, (![C_52, A_53]: (~r1_tarski(C_52, A_53) | '#skF_1'(k1_zfmisc_1(A_53))='#skF_5' | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_182, c_87])).
% 2.38/1.35  tff(c_206, plain, (![A_56]: ('#skF_1'(k1_zfmisc_1(A_56))='#skF_5' | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_119, c_190])).
% 2.38/1.35  tff(c_228, plain, (![A_57]: (r1_tarski('#skF_5', A_57) | v1_xboole_0(k1_zfmisc_1(A_57)) | ~v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_206, c_98])).
% 2.38/1.35  tff(c_236, plain, (![C_58, A_59]: (~r1_tarski(C_58, A_59) | r1_tarski('#skF_5', A_59) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_228, c_87])).
% 2.38/1.35  tff(c_244, plain, (![A_5]: (r1_tarski('#skF_5', A_5) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_119, c_236])).
% 2.38/1.35  tff(c_326, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_2'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_10, c_121])).
% 2.38/1.35  tff(c_344, plain, (![B_82, A_83, B_84]: (~v1_xboole_0(B_82) | ~r1_tarski(A_83, B_82) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_326, c_2])).
% 2.38/1.35  tff(c_368, plain, (![B_84, A_5]: (r1_tarski('#skF_5', B_84) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_244, c_344])).
% 2.38/1.35  tff(c_385, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitLeft, [status(thm)], [c_368])).
% 2.38/1.35  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_385, c_34])).
% 2.38/1.35  tff(c_396, plain, (![B_84]: (r1_tarski('#skF_5', B_84))), inference(splitRight, [status(thm)], [c_368])).
% 2.38/1.35  tff(c_16, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.35  tff(c_26, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.35  tff(c_38, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.38/1.35  tff(c_41, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38])).
% 2.38/1.35  tff(c_36, plain, (![A_17]: (k3_yellow_0(k2_yellow_1(A_17))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.38/1.35  tff(c_134, plain, (![A_43]: (k3_yellow_0(k2_yellow_1(A_43))='#skF_5' | ~r2_hidden('#skF_5', A_43) | v1_xboole_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_36])).
% 2.38/1.35  tff(c_420, plain, (![A_91]: (k3_yellow_0(k3_yellow_1(A_91))='#skF_5' | ~r2_hidden('#skF_5', k1_zfmisc_1(A_91)) | v1_xboole_0(k1_zfmisc_1(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_134])).
% 2.38/1.35  tff(c_427, plain, (![A_11]: (k3_yellow_0(k3_yellow_1(A_11))='#skF_5' | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski('#skF_5', A_11))), inference(resolution, [status(thm)], [c_16, c_420])).
% 2.38/1.35  tff(c_447, plain, (![A_94]: (k3_yellow_0(k3_yellow_1(A_94))='#skF_5' | v1_xboole_0(k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_427])).
% 2.38/1.35  tff(c_455, plain, (![C_95, A_96]: (~r1_tarski(C_95, A_96) | k3_yellow_0(k3_yellow_1(A_96))='#skF_5')), inference(resolution, [status(thm)], [c_447, c_87])).
% 2.38/1.35  tff(c_485, plain, (![B_84]: (k3_yellow_0(k3_yellow_1(B_84))='#skF_5')), inference(resolution, [status(thm)], [c_396, c_455])).
% 2.38/1.35  tff(c_40, plain, (k3_yellow_0(k3_yellow_1('#skF_6'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.38/1.35  tff(c_57, plain, (k3_yellow_0(k3_yellow_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_40])).
% 2.38/1.35  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_57])).
% 2.38/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  Inference rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Ref     : 0
% 2.38/1.35  #Sup     : 106
% 2.38/1.35  #Fact    : 0
% 2.38/1.35  #Define  : 0
% 2.38/1.35  #Split   : 1
% 2.38/1.35  #Chain   : 0
% 2.38/1.35  #Close   : 0
% 2.38/1.35  
% 2.38/1.35  Ordering : KBO
% 2.38/1.35  
% 2.38/1.35  Simplification rules
% 2.38/1.35  ----------------------
% 2.38/1.35  #Subsume      : 32
% 2.38/1.35  #Demod        : 16
% 2.38/1.35  #Tautology    : 27
% 2.38/1.35  #SimpNegUnit  : 9
% 2.38/1.35  #BackRed      : 9
% 2.38/1.35  
% 2.38/1.35  #Partial instantiations: 0
% 2.38/1.35  #Strategies tried      : 1
% 2.38/1.35  
% 2.38/1.35  Timing (in seconds)
% 2.38/1.35  ----------------------
% 2.38/1.35  Preprocessing        : 0.30
% 2.38/1.35  Parsing              : 0.15
% 2.38/1.35  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.29
% 2.38/1.35  Inferencing          : 0.11
% 2.38/1.35  Reduction            : 0.07
% 2.38/1.35  Demodulation         : 0.05
% 2.38/1.35  BG Simplification    : 0.02
% 2.38/1.35  Subsumption          : 0.07
% 2.38/1.35  Abstraction          : 0.02
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.36  Cooper               : 0.00
% 2.38/1.36  Total                : 0.62
% 2.38/1.36  Index Insertion      : 0.00
% 2.38/1.36  Index Deletion       : 0.00
% 2.38/1.36  Index Matching       : 0.00
% 2.38/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
