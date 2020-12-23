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
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 167 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 424 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_36,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'(A_13),A_13)
      | v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    ! [A_34,B_35] :
      ( v3_ordinal1(A_34)
      | ~ r2_hidden(A_34,B_35)
      | ~ v3_ordinal1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    ! [A_13] :
      ( v3_ordinal1('#skF_2'(A_13))
      | ~ v3_ordinal1(A_13)
      | v1_ordinal1(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_ordinal1(B_12,A_11)
      | r1_ordinal1(A_11,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_ordinal1(A_54,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ r1_tarski('#skF_2'(A_13),A_13)
      | v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    ! [B_65] :
      ( v1_ordinal1(B_65)
      | ~ r1_ordinal1('#skF_2'(B_65),B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1('#skF_2'(B_65)) ) ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_360,plain,(
    ! [A_86] :
      ( v1_ordinal1(A_86)
      | r1_ordinal1(A_86,'#skF_2'(A_86))
      | ~ v3_ordinal1('#skF_2'(A_86))
      | ~ v3_ordinal1(A_86) ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_41,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    ! [A_13] :
      ( ~ r1_tarski(A_13,'#skF_2'(A_13))
      | v1_ordinal1(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_114,plain,(
    ! [A_54] :
      ( v1_ordinal1(A_54)
      | ~ r1_ordinal1(A_54,'#skF_2'(A_54))
      | ~ v3_ordinal1('#skF_2'(A_54))
      | ~ v3_ordinal1(A_54) ) ),
    inference(resolution,[status(thm)],[c_97,c_45])).

tff(c_365,plain,(
    ! [A_87] :
      ( v1_ordinal1(A_87)
      | ~ v3_ordinal1('#skF_2'(A_87))
      | ~ v3_ordinal1(A_87) ) ),
    inference(resolution,[status(thm)],[c_360,c_114])).

tff(c_387,plain,(
    ! [A_91] :
      ( ~ v3_ordinal1(A_91)
      | v1_ordinal1(A_91) ) ),
    inference(resolution,[status(thm)],[c_51,c_365])).

tff(c_399,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_387])).

tff(c_71,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(k3_tarski(A_45),B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_16,A_13] :
      ( r1_tarski(B_16,A_13)
      | ~ r2_hidden(B_16,A_13)
      | ~ v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_247,plain,(
    ! [A_74,B_75] :
      ( r1_tarski('#skF_1'(A_74,B_75),A_74)
      | ~ v1_ordinal1(A_74)
      | r1_tarski(k3_tarski(A_74),B_75) ) ),
    inference(resolution,[status(thm)],[c_71,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [A_76] :
      ( ~ v1_ordinal1(A_76)
      | r1_tarski(k3_tarski(A_76),A_76) ) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k3_tarski(A_6),k3_tarski(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [C_47,B_48,A_49] :
      ( r1_tarski(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(k3_tarski(A_49),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_61,B_62] :
      ( r1_tarski('#skF_2'(A_61),B_62)
      | ~ r1_tarski(k3_tarski(A_61),B_62)
      | v1_ordinal1(A_61) ) ),
    inference(resolution,[status(thm)],[c_22,c_84])).

tff(c_180,plain,(
    ! [A_66,B_67] :
      ( r1_tarski('#skF_2'(A_66),k3_tarski(B_67))
      | v1_ordinal1(A_66)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_189,plain,(
    ! [B_67] :
      ( v1_ordinal1(k3_tarski(B_67))
      | ~ r1_tarski(k3_tarski(B_67),B_67) ) ),
    inference(resolution,[status(thm)],[c_180,c_20])).

tff(c_303,plain,(
    ! [A_76] :
      ( v1_ordinal1(k3_tarski(A_76))
      | ~ v1_ordinal1(A_76) ) ),
    inference(resolution,[status(thm)],[c_284,c_189])).

tff(c_277,plain,(
    ! [A_74] :
      ( ~ v1_ordinal1(A_74)
      | r1_tarski(k3_tarski(A_74),A_74) ) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(A_52,B_53)
      | ~ r2_xboole_0(A_52,B_53)
      | ~ v3_ordinal1(B_53)
      | ~ v1_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_306,plain,(
    ! [A_77,B_78] :
      ( r2_hidden(A_77,B_78)
      | ~ v3_ordinal1(B_78)
      | ~ v1_ordinal1(A_77)
      | B_78 = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( v3_ordinal1(A_22)
      | ~ r2_hidden(A_22,B_23)
      | ~ v3_ordinal1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_325,plain,(
    ! [A_82,B_83] :
      ( v3_ordinal1(A_82)
      | ~ v3_ordinal1(B_83)
      | ~ v1_ordinal1(A_82)
      | B_83 = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_306,c_30])).

tff(c_539,plain,(
    ! [A_115] :
      ( v3_ordinal1(k3_tarski(A_115))
      | ~ v3_ordinal1(A_115)
      | ~ v1_ordinal1(k3_tarski(A_115))
      | k3_tarski(A_115) = A_115
      | ~ v1_ordinal1(A_115) ) ),
    inference(resolution,[status(thm)],[c_277,c_325])).

tff(c_34,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_545,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1(k3_tarski('#skF_3'))
    | k3_tarski('#skF_3') = '#skF_3'
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_539,c_34])).

tff(c_549,plain,
    ( ~ v1_ordinal1(k3_tarski('#skF_3'))
    | k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_36,c_545])).

tff(c_550,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_556,plain,(
    ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_550])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_556])).

tff(c_564,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_566,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_34])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:20:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.39  
% 3.03/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.39  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 3.03/1.39  
% 3.03/1.39  %Foreground sorts:
% 3.03/1.39  
% 3.03/1.39  
% 3.03/1.39  %Background operators:
% 3.03/1.39  
% 3.03/1.39  
% 3.03/1.39  %Foreground operators:
% 3.03/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.03/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.39  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.03/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.39  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.03/1.39  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.39  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.03/1.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.03/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.03/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.03/1.39  
% 3.03/1.40  tff(f_97, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 3.03/1.40  tff(f_64, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 3.03/1.40  tff(f_87, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.03/1.40  tff(f_57, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.03/1.40  tff(f_72, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.03/1.40  tff(f_92, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.03/1.40  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 3.03/1.40  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.03/1.40  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 3.03/1.40  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.03/1.40  tff(f_81, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 3.03/1.40  tff(c_36, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.40  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_2'(A_13), A_13) | v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.40  tff(c_47, plain, (![A_34, B_35]: (v3_ordinal1(A_34) | ~r2_hidden(A_34, B_35) | ~v3_ordinal1(B_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.40  tff(c_51, plain, (![A_13]: (v3_ordinal1('#skF_2'(A_13)) | ~v3_ordinal1(A_13) | v1_ordinal1(A_13))), inference(resolution, [status(thm)], [c_22, c_47])).
% 3.03/1.40  tff(c_16, plain, (![B_12, A_11]: (r1_ordinal1(B_12, A_11) | r1_ordinal1(A_11, B_12) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.03/1.40  tff(c_97, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~r1_ordinal1(A_54, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.03/1.40  tff(c_20, plain, (![A_13]: (~r1_tarski('#skF_2'(A_13), A_13) | v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.40  tff(c_169, plain, (![B_65]: (v1_ordinal1(B_65) | ~r1_ordinal1('#skF_2'(B_65), B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1('#skF_2'(B_65)))), inference(resolution, [status(thm)], [c_97, c_20])).
% 3.03/1.40  tff(c_360, plain, (![A_86]: (v1_ordinal1(A_86) | r1_ordinal1(A_86, '#skF_2'(A_86)) | ~v3_ordinal1('#skF_2'(A_86)) | ~v3_ordinal1(A_86))), inference(resolution, [status(thm)], [c_16, c_169])).
% 3.03/1.40  tff(c_41, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.40  tff(c_45, plain, (![A_13]: (~r1_tarski(A_13, '#skF_2'(A_13)) | v1_ordinal1(A_13))), inference(resolution, [status(thm)], [c_22, c_41])).
% 3.03/1.40  tff(c_114, plain, (![A_54]: (v1_ordinal1(A_54) | ~r1_ordinal1(A_54, '#skF_2'(A_54)) | ~v3_ordinal1('#skF_2'(A_54)) | ~v3_ordinal1(A_54))), inference(resolution, [status(thm)], [c_97, c_45])).
% 3.03/1.40  tff(c_365, plain, (![A_87]: (v1_ordinal1(A_87) | ~v3_ordinal1('#skF_2'(A_87)) | ~v3_ordinal1(A_87))), inference(resolution, [status(thm)], [c_360, c_114])).
% 3.03/1.40  tff(c_387, plain, (![A_91]: (~v3_ordinal1(A_91) | v1_ordinal1(A_91))), inference(resolution, [status(thm)], [c_51, c_365])).
% 3.03/1.40  tff(c_399, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_387])).
% 3.03/1.40  tff(c_71, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(k3_tarski(A_45), B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.03/1.40  tff(c_18, plain, (![B_16, A_13]: (r1_tarski(B_16, A_13) | ~r2_hidden(B_16, A_13) | ~v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.40  tff(c_247, plain, (![A_74, B_75]: (r1_tarski('#skF_1'(A_74, B_75), A_74) | ~v1_ordinal1(A_74) | r1_tarski(k3_tarski(A_74), B_75))), inference(resolution, [status(thm)], [c_71, c_18])).
% 3.03/1.40  tff(c_8, plain, (![A_3, B_4]: (~r1_tarski('#skF_1'(A_3, B_4), B_4) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.03/1.40  tff(c_284, plain, (![A_76]: (~v1_ordinal1(A_76) | r1_tarski(k3_tarski(A_76), A_76))), inference(resolution, [status(thm)], [c_247, c_8])).
% 3.03/1.40  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k3_tarski(A_6), k3_tarski(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.03/1.40  tff(c_84, plain, (![C_47, B_48, A_49]: (r1_tarski(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(k3_tarski(A_49), B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.03/1.40  tff(c_141, plain, (![A_61, B_62]: (r1_tarski('#skF_2'(A_61), B_62) | ~r1_tarski(k3_tarski(A_61), B_62) | v1_ordinal1(A_61))), inference(resolution, [status(thm)], [c_22, c_84])).
% 3.03/1.40  tff(c_180, plain, (![A_66, B_67]: (r1_tarski('#skF_2'(A_66), k3_tarski(B_67)) | v1_ordinal1(A_66) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_12, c_141])).
% 3.03/1.40  tff(c_189, plain, (![B_67]: (v1_ordinal1(k3_tarski(B_67)) | ~r1_tarski(k3_tarski(B_67), B_67))), inference(resolution, [status(thm)], [c_180, c_20])).
% 3.03/1.40  tff(c_303, plain, (![A_76]: (v1_ordinal1(k3_tarski(A_76)) | ~v1_ordinal1(A_76))), inference(resolution, [status(thm)], [c_284, c_189])).
% 3.03/1.40  tff(c_277, plain, (![A_74]: (~v1_ordinal1(A_74) | r1_tarski(k3_tarski(A_74), A_74))), inference(resolution, [status(thm)], [c_247, c_8])).
% 3.03/1.40  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.03/1.40  tff(c_92, plain, (![A_52, B_53]: (r2_hidden(A_52, B_53) | ~r2_xboole_0(A_52, B_53) | ~v3_ordinal1(B_53) | ~v1_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.03/1.40  tff(c_306, plain, (![A_77, B_78]: (r2_hidden(A_77, B_78) | ~v3_ordinal1(B_78) | ~v1_ordinal1(A_77) | B_78=A_77 | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_2, c_92])).
% 3.03/1.40  tff(c_30, plain, (![A_22, B_23]: (v3_ordinal1(A_22) | ~r2_hidden(A_22, B_23) | ~v3_ordinal1(B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.40  tff(c_325, plain, (![A_82, B_83]: (v3_ordinal1(A_82) | ~v3_ordinal1(B_83) | ~v1_ordinal1(A_82) | B_83=A_82 | ~r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_306, c_30])).
% 3.03/1.40  tff(c_539, plain, (![A_115]: (v3_ordinal1(k3_tarski(A_115)) | ~v3_ordinal1(A_115) | ~v1_ordinal1(k3_tarski(A_115)) | k3_tarski(A_115)=A_115 | ~v1_ordinal1(A_115))), inference(resolution, [status(thm)], [c_277, c_325])).
% 3.03/1.40  tff(c_34, plain, (~v3_ordinal1(k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.40  tff(c_545, plain, (~v3_ordinal1('#skF_3') | ~v1_ordinal1(k3_tarski('#skF_3')) | k3_tarski('#skF_3')='#skF_3' | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_539, c_34])).
% 3.03/1.40  tff(c_549, plain, (~v1_ordinal1(k3_tarski('#skF_3')) | k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_399, c_36, c_545])).
% 3.03/1.40  tff(c_550, plain, (~v1_ordinal1(k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_549])).
% 3.03/1.40  tff(c_556, plain, (~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_303, c_550])).
% 3.03/1.40  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_556])).
% 3.03/1.40  tff(c_564, plain, (k3_tarski('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_549])).
% 3.03/1.40  tff(c_566, plain, (~v3_ordinal1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_34])).
% 3.03/1.40  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_566])).
% 3.03/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.40  
% 3.03/1.40  Inference rules
% 3.03/1.40  ----------------------
% 3.03/1.40  #Ref     : 0
% 3.03/1.40  #Sup     : 109
% 3.03/1.40  #Fact    : 2
% 3.03/1.40  #Define  : 0
% 3.03/1.40  #Split   : 1
% 3.03/1.40  #Chain   : 0
% 3.03/1.40  #Close   : 0
% 3.03/1.40  
% 3.03/1.40  Ordering : KBO
% 3.03/1.40  
% 3.03/1.40  Simplification rules
% 3.03/1.40  ----------------------
% 3.03/1.40  #Subsume      : 19
% 3.03/1.40  #Demod        : 6
% 3.03/1.40  #Tautology    : 8
% 3.03/1.40  #SimpNegUnit  : 0
% 3.03/1.40  #BackRed      : 1
% 3.03/1.40  
% 3.03/1.40  #Partial instantiations: 0
% 3.03/1.40  #Strategies tried      : 1
% 3.03/1.40  
% 3.03/1.40  Timing (in seconds)
% 3.03/1.40  ----------------------
% 3.03/1.41  Preprocessing        : 0.29
% 3.03/1.41  Parsing              : 0.16
% 3.03/1.41  CNF conversion       : 0.02
% 3.03/1.41  Main loop            : 0.36
% 3.03/1.41  Inferencing          : 0.15
% 3.03/1.41  Reduction            : 0.07
% 3.03/1.41  Demodulation         : 0.05
% 3.03/1.41  BG Simplification    : 0.02
% 3.03/1.41  Subsumption          : 0.09
% 3.03/1.41  Abstraction          : 0.01
% 3.03/1.41  MUC search           : 0.00
% 3.03/1.41  Cooper               : 0.00
% 3.03/1.41  Total                : 0.68
% 3.03/1.41  Index Insertion      : 0.00
% 3.03/1.41  Index Deletion       : 0.00
% 3.03/1.41  Index Matching       : 0.00
% 3.03/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
