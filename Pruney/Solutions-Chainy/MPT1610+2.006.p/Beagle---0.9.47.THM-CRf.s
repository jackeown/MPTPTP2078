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
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 249 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  106 ( 495 expanded)
%              Number of equality atoms :   25 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

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

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_62,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_2'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [C_30,A_31] :
      ( r1_tarski(C_30,A_31)
      | ~ r2_hidden(C_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [A_31] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_31)),A_31)
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_130,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44),B_45)
      | ~ r1_tarski(A_44,B_45)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_47,B_46)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_166,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_48)))
      | v1_xboole_0(k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_92,c_153])).

tff(c_14,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_45])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_10] :
      ( A_10 = '#skF_3'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_12])).

tff(c_171,plain,(
    ! [A_49] :
      ( '#skF_1'(k1_zfmisc_1(A_49)) = '#skF_3'
      | ~ v1_xboole_0(A_49)
      | v1_xboole_0(k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_166,c_50])).

tff(c_77,plain,(
    ! [C_26,A_27] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [A_27,C_26] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_179,plain,(
    ! [C_50,A_51] :
      ( ~ r1_tarski(C_50,A_51)
      | '#skF_1'(k1_zfmisc_1(A_51)) = '#skF_3'
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_171,c_81])).

tff(c_202,plain,(
    ! [A_54] :
      ( '#skF_1'(k1_zfmisc_1(A_54)) = '#skF_3'
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_113,c_179])).

tff(c_224,plain,(
    ! [A_55] :
      ( r1_tarski('#skF_3',A_55)
      | v1_xboole_0(k1_zfmisc_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_92])).

tff(c_238,plain,(
    ! [C_58,A_59] :
      ( ~ r1_tarski(C_58,A_59)
      | r1_tarski('#skF_3',A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_224,c_81])).

tff(c_246,plain,(
    ! [A_5] :
      ( r1_tarski('#skF_3',A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_113,c_238])).

tff(c_328,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_2'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_130])).

tff(c_361,plain,(
    ! [B_84,A_85,B_86] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_328,c_2])).

tff(c_388,plain,(
    ! [B_86,A_5] :
      ( r1_tarski('#skF_3',B_86)
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_246,c_361])).

tff(c_392,plain,(
    ! [A_5] : ~ v1_xboole_0(A_5) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_14])).

tff(c_403,plain,(
    ! [B_86] : r1_tarski('#skF_3',B_86) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_18,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_30,plain,(
    ! [A_17] :
      ( k3_yellow_0(k2_yellow_1(A_17)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_118,plain,(
    ! [A_40] :
      ( k3_yellow_0(k2_yellow_1(A_40)) = '#skF_3'
      | ~ r2_hidden('#skF_3',A_40)
      | v1_xboole_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_49,c_30])).

tff(c_435,plain,(
    ! [A_92] :
      ( k3_yellow_0(k3_yellow_1(A_92)) = '#skF_3'
      | ~ r2_hidden('#skF_3',k1_zfmisc_1(A_92))
      | v1_xboole_0(k1_zfmisc_1(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_118])).

tff(c_442,plain,(
    ! [A_11] :
      ( k3_yellow_0(k3_yellow_1(A_11)) = '#skF_3'
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski('#skF_3',A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_435])).

tff(c_447,plain,(
    ! [A_93] :
      ( k3_yellow_0(k3_yellow_1(A_93)) = '#skF_3'
      | v1_xboole_0(k1_zfmisc_1(A_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_442])).

tff(c_455,plain,(
    ! [C_94,A_95] :
      ( ~ r1_tarski(C_94,A_95)
      | k3_yellow_0(k3_yellow_1(A_95)) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_447,c_81])).

tff(c_481,plain,(
    ! [B_86] : k3_yellow_0(k3_yellow_1(B_86)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_403,c_455])).

tff(c_34,plain,(
    k3_yellow_0(k3_yellow_1('#skF_6')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    k3_yellow_0(k3_yellow_1('#skF_6')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_34])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_51])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.38  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.53/1.38  
% 2.53/1.38  %Foreground sorts:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Background operators:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Foreground operators:
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.38  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.53/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.38  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.53/1.38  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.53/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.38  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.53/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.53/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.53/1.38  
% 2.53/1.39  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.53/1.39  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.53/1.39  tff(f_44, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.53/1.39  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.39  tff(f_53, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.53/1.39  tff(f_62, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.53/1.39  tff(f_60, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 2.53/1.39  tff(f_65, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 2.53/1.39  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.39  tff(c_104, plain, (![A_36, B_37]: (~r2_hidden('#skF_2'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.39  tff(c_113, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_104])).
% 2.53/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.39  tff(c_83, plain, (![C_30, A_31]: (r1_tarski(C_30, A_31) | ~r2_hidden(C_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.39  tff(c_92, plain, (![A_31]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_31)), A_31) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.53/1.39  tff(c_130, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.39  tff(c_140, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44), B_45) | ~r1_tarski(A_44, B_45) | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_4, c_130])).
% 2.53/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.39  tff(c_153, plain, (![B_46, A_47]: (~v1_xboole_0(B_46) | ~r1_tarski(A_47, B_46) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_140, c_2])).
% 2.53/1.39  tff(c_166, plain, (![A_48]: (~v1_xboole_0(A_48) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_48))) | v1_xboole_0(k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_92, c_153])).
% 2.53/1.39  tff(c_14, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.39  tff(c_45, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.39  tff(c_49, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_45])).
% 2.53/1.39  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.39  tff(c_50, plain, (![A_10]: (A_10='#skF_3' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_12])).
% 2.53/1.39  tff(c_171, plain, (![A_49]: ('#skF_1'(k1_zfmisc_1(A_49))='#skF_3' | ~v1_xboole_0(A_49) | v1_xboole_0(k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_166, c_50])).
% 2.53/1.39  tff(c_77, plain, (![C_26, A_27]: (r2_hidden(C_26, k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.39  tff(c_81, plain, (![A_27, C_26]: (~v1_xboole_0(k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(resolution, [status(thm)], [c_77, c_2])).
% 2.53/1.39  tff(c_179, plain, (![C_50, A_51]: (~r1_tarski(C_50, A_51) | '#skF_1'(k1_zfmisc_1(A_51))='#skF_3' | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_171, c_81])).
% 2.53/1.39  tff(c_202, plain, (![A_54]: ('#skF_1'(k1_zfmisc_1(A_54))='#skF_3' | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_113, c_179])).
% 2.53/1.39  tff(c_224, plain, (![A_55]: (r1_tarski('#skF_3', A_55) | v1_xboole_0(k1_zfmisc_1(A_55)) | ~v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_202, c_92])).
% 2.53/1.39  tff(c_238, plain, (![C_58, A_59]: (~r1_tarski(C_58, A_59) | r1_tarski('#skF_3', A_59) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_224, c_81])).
% 2.53/1.39  tff(c_246, plain, (![A_5]: (r1_tarski('#skF_3', A_5) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_113, c_238])).
% 2.53/1.39  tff(c_328, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_2'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_10, c_130])).
% 2.53/1.39  tff(c_361, plain, (![B_84, A_85, B_86]: (~v1_xboole_0(B_84) | ~r1_tarski(A_85, B_84) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_328, c_2])).
% 2.53/1.39  tff(c_388, plain, (![B_86, A_5]: (r1_tarski('#skF_3', B_86) | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_246, c_361])).
% 2.53/1.39  tff(c_392, plain, (![A_5]: (~v1_xboole_0(A_5))), inference(splitLeft, [status(thm)], [c_388])).
% 2.53/1.39  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_392, c_14])).
% 2.53/1.39  tff(c_403, plain, (![B_86]: (r1_tarski('#skF_3', B_86))), inference(splitRight, [status(thm)], [c_388])).
% 2.53/1.39  tff(c_18, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.39  tff(c_28, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.39  tff(c_32, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.39  tff(c_35, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.53/1.39  tff(c_30, plain, (![A_17]: (k3_yellow_0(k2_yellow_1(A_17))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.39  tff(c_118, plain, (![A_40]: (k3_yellow_0(k2_yellow_1(A_40))='#skF_3' | ~r2_hidden('#skF_3', A_40) | v1_xboole_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_49, c_30])).
% 2.53/1.39  tff(c_435, plain, (![A_92]: (k3_yellow_0(k3_yellow_1(A_92))='#skF_3' | ~r2_hidden('#skF_3', k1_zfmisc_1(A_92)) | v1_xboole_0(k1_zfmisc_1(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_118])).
% 2.53/1.39  tff(c_442, plain, (![A_11]: (k3_yellow_0(k3_yellow_1(A_11))='#skF_3' | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski('#skF_3', A_11))), inference(resolution, [status(thm)], [c_18, c_435])).
% 2.53/1.39  tff(c_447, plain, (![A_93]: (k3_yellow_0(k3_yellow_1(A_93))='#skF_3' | v1_xboole_0(k1_zfmisc_1(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_442])).
% 2.53/1.39  tff(c_455, plain, (![C_94, A_95]: (~r1_tarski(C_94, A_95) | k3_yellow_0(k3_yellow_1(A_95))='#skF_3')), inference(resolution, [status(thm)], [c_447, c_81])).
% 2.53/1.39  tff(c_481, plain, (![B_86]: (k3_yellow_0(k3_yellow_1(B_86))='#skF_3')), inference(resolution, [status(thm)], [c_403, c_455])).
% 2.53/1.39  tff(c_34, plain, (k3_yellow_0(k3_yellow_1('#skF_6'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.39  tff(c_51, plain, (k3_yellow_0(k3_yellow_1('#skF_6'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_34])).
% 2.53/1.39  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_51])).
% 2.53/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  Inference rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Ref     : 0
% 2.53/1.39  #Sup     : 108
% 2.53/1.39  #Fact    : 0
% 2.53/1.39  #Define  : 0
% 2.53/1.39  #Split   : 1
% 2.53/1.39  #Chain   : 0
% 2.53/1.39  #Close   : 0
% 2.53/1.39  
% 2.53/1.39  Ordering : KBO
% 2.53/1.39  
% 2.53/1.39  Simplification rules
% 2.53/1.39  ----------------------
% 2.53/1.39  #Subsume      : 32
% 2.53/1.39  #Demod        : 16
% 2.53/1.39  #Tautology    : 28
% 2.53/1.39  #SimpNegUnit  : 9
% 2.53/1.39  #BackRed      : 9
% 2.53/1.39  
% 2.53/1.39  #Partial instantiations: 0
% 2.53/1.39  #Strategies tried      : 1
% 2.53/1.39  
% 2.53/1.39  Timing (in seconds)
% 2.53/1.39  ----------------------
% 2.53/1.40  Preprocessing        : 0.30
% 2.53/1.40  Parsing              : 0.16
% 2.53/1.40  CNF conversion       : 0.02
% 2.53/1.40  Main loop            : 0.29
% 2.53/1.40  Inferencing          : 0.11
% 2.53/1.40  Reduction            : 0.07
% 2.53/1.40  Demodulation         : 0.05
% 2.53/1.40  BG Simplification    : 0.02
% 2.53/1.40  Subsumption          : 0.07
% 2.53/1.40  Abstraction          : 0.02
% 2.53/1.40  MUC search           : 0.00
% 2.53/1.40  Cooper               : 0.00
% 2.53/1.40  Total                : 0.62
% 2.53/1.40  Index Insertion      : 0.00
% 2.53/1.40  Index Deletion       : 0.00
% 2.53/1.40  Index Matching       : 0.00
% 2.53/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
