%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 227 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_81,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_57,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_30,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_24] :
      ( v3_ordinal1(k1_ordinal1(A_24))
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_31,plain,(
    ! [A_25] :
      ( v1_ordinal1(A_25)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_35,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_31])).

tff(c_80,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),A_41)
      | r1_tarski(k3_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_13,A_10] :
      ( r1_tarski(B_13,A_10)
      | ~ r2_hidden(B_13,A_10)
      | ~ v1_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    ! [A_70,B_71] :
      ( r1_tarski('#skF_1'(A_70,B_71),A_70)
      | ~ v1_ordinal1(A_70)
      | r1_tarski(k3_tarski(A_70),B_71) ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(k3_tarski(A_1),B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_255,plain,(
    ! [A_72] :
      ( ~ v1_ordinal1(A_72)
      | r1_tarski(k3_tarski(A_72),A_72) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k3_tarski(A_4),k3_tarski(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | v1_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [C_45,B_46,A_47] :
      ( r1_tarski(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(k3_tarski(A_47),B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [A_54,B_55] :
      ( r1_tarski('#skF_2'(A_54),B_55)
      | ~ r1_tarski(k3_tarski(A_54),B_55)
      | v1_ordinal1(A_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_90])).

tff(c_137,plain,(
    ! [A_56,B_57] :
      ( r1_tarski('#skF_2'(A_56),k3_tarski(B_57))
      | v1_ordinal1(A_56)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ r1_tarski('#skF_2'(A_10),A_10)
      | v1_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_142,plain,(
    ! [B_57] :
      ( v1_ordinal1(k3_tarski(B_57))
      | ~ r1_tarski(k3_tarski(B_57),B_57) ) ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_275,plain,(
    ! [A_72] :
      ( v1_ordinal1(k3_tarski(A_72))
      | ~ v1_ordinal1(A_72) ) ),
    inference(resolution,[status(thm)],[c_255,c_142])).

tff(c_249,plain,(
    ! [A_70] :
      ( ~ v1_ordinal1(A_70)
      | r1_tarski(k3_tarski(A_70),A_70) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_20,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_143,plain,(
    ! [A_58,C_59,B_60] :
      ( r2_hidden(A_58,C_59)
      | ~ r2_hidden(B_60,C_59)
      | ~ r1_tarski(A_58,B_60)
      | ~ v3_ordinal1(C_59)
      | ~ v3_ordinal1(B_60)
      | ~ v1_ordinal1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_364,plain,(
    ! [A_94,A_95] :
      ( r2_hidden(A_94,k1_ordinal1(A_95))
      | ~ r1_tarski(A_94,A_95)
      | ~ v3_ordinal1(k1_ordinal1(A_95))
      | ~ v3_ordinal1(A_95)
      | ~ v1_ordinal1(A_94) ) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( v3_ordinal1(A_22)
      | ~ r2_hidden(A_22,B_23)
      | ~ v3_ordinal1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_380,plain,(
    ! [A_97,A_98] :
      ( v3_ordinal1(A_97)
      | ~ r1_tarski(A_97,A_98)
      | ~ v3_ordinal1(k1_ordinal1(A_98))
      | ~ v3_ordinal1(A_98)
      | ~ v1_ordinal1(A_97) ) ),
    inference(resolution,[status(thm)],[c_364,c_24])).

tff(c_461,plain,(
    ! [A_110] :
      ( v3_ordinal1(k3_tarski(A_110))
      | ~ v3_ordinal1(k1_ordinal1(A_110))
      | ~ v3_ordinal1(A_110)
      | ~ v1_ordinal1(k3_tarski(A_110))
      | ~ v1_ordinal1(A_110) ) ),
    inference(resolution,[status(thm)],[c_249,c_380])).

tff(c_28,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_470,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1(k3_tarski('#skF_3'))
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_461,c_28])).

tff(c_475,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v1_ordinal1(k3_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_30,c_470])).

tff(c_476,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_479,plain,(
    ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_476])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_479])).

tff(c_487,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_491,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_487])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:31:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  %$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.42  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.42  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.76/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.42  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.76/1.42  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.42  
% 2.76/1.43  tff(f_86, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 2.76/1.43  tff(f_81, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.76/1.43  tff(f_48, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.76/1.43  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.76/1.43  tff(f_55, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.76/1.43  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.76/1.43  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.76/1.43  tff(f_57, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.76/1.43  tff(f_71, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.76/1.43  tff(f_77, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.76/1.43  tff(c_30, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.43  tff(c_26, plain, (![A_24]: (v3_ordinal1(k1_ordinal1(A_24)) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.43  tff(c_31, plain, (![A_25]: (v1_ordinal1(A_25) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.43  tff(c_35, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_31])).
% 2.76/1.43  tff(c_80, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), A_41) | r1_tarski(k3_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.43  tff(c_14, plain, (![B_13, A_10]: (r1_tarski(B_13, A_10) | ~r2_hidden(B_13, A_10) | ~v1_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.43  tff(c_227, plain, (![A_70, B_71]: (r1_tarski('#skF_1'(A_70, B_71), A_70) | ~v1_ordinal1(A_70) | r1_tarski(k3_tarski(A_70), B_71))), inference(resolution, [status(thm)], [c_80, c_14])).
% 2.76/1.43  tff(c_2, plain, (![A_1, B_2]: (~r1_tarski('#skF_1'(A_1, B_2), B_2) | r1_tarski(k3_tarski(A_1), B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.43  tff(c_255, plain, (![A_72]: (~v1_ordinal1(A_72) | r1_tarski(k3_tarski(A_72), A_72))), inference(resolution, [status(thm)], [c_227, c_2])).
% 2.76/1.43  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k3_tarski(A_4), k3_tarski(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.43  tff(c_18, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | v1_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.43  tff(c_90, plain, (![C_45, B_46, A_47]: (r1_tarski(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(k3_tarski(A_47), B_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.43  tff(c_123, plain, (![A_54, B_55]: (r1_tarski('#skF_2'(A_54), B_55) | ~r1_tarski(k3_tarski(A_54), B_55) | v1_ordinal1(A_54))), inference(resolution, [status(thm)], [c_18, c_90])).
% 2.76/1.43  tff(c_137, plain, (![A_56, B_57]: (r1_tarski('#skF_2'(A_56), k3_tarski(B_57)) | v1_ordinal1(A_56) | ~r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.76/1.43  tff(c_16, plain, (![A_10]: (~r1_tarski('#skF_2'(A_10), A_10) | v1_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.43  tff(c_142, plain, (![B_57]: (v1_ordinal1(k3_tarski(B_57)) | ~r1_tarski(k3_tarski(B_57), B_57))), inference(resolution, [status(thm)], [c_137, c_16])).
% 2.76/1.43  tff(c_275, plain, (![A_72]: (v1_ordinal1(k3_tarski(A_72)) | ~v1_ordinal1(A_72))), inference(resolution, [status(thm)], [c_255, c_142])).
% 2.76/1.43  tff(c_249, plain, (![A_70]: (~v1_ordinal1(A_70) | r1_tarski(k3_tarski(A_70), A_70))), inference(resolution, [status(thm)], [c_227, c_2])).
% 2.76/1.43  tff(c_20, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.76/1.43  tff(c_143, plain, (![A_58, C_59, B_60]: (r2_hidden(A_58, C_59) | ~r2_hidden(B_60, C_59) | ~r1_tarski(A_58, B_60) | ~v3_ordinal1(C_59) | ~v3_ordinal1(B_60) | ~v1_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.43  tff(c_364, plain, (![A_94, A_95]: (r2_hidden(A_94, k1_ordinal1(A_95)) | ~r1_tarski(A_94, A_95) | ~v3_ordinal1(k1_ordinal1(A_95)) | ~v3_ordinal1(A_95) | ~v1_ordinal1(A_94))), inference(resolution, [status(thm)], [c_20, c_143])).
% 2.76/1.43  tff(c_24, plain, (![A_22, B_23]: (v3_ordinal1(A_22) | ~r2_hidden(A_22, B_23) | ~v3_ordinal1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.76/1.43  tff(c_380, plain, (![A_97, A_98]: (v3_ordinal1(A_97) | ~r1_tarski(A_97, A_98) | ~v3_ordinal1(k1_ordinal1(A_98)) | ~v3_ordinal1(A_98) | ~v1_ordinal1(A_97))), inference(resolution, [status(thm)], [c_364, c_24])).
% 2.76/1.43  tff(c_461, plain, (![A_110]: (v3_ordinal1(k3_tarski(A_110)) | ~v3_ordinal1(k1_ordinal1(A_110)) | ~v3_ordinal1(A_110) | ~v1_ordinal1(k3_tarski(A_110)) | ~v1_ordinal1(A_110))), inference(resolution, [status(thm)], [c_249, c_380])).
% 2.76/1.43  tff(c_28, plain, (~v3_ordinal1(k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.43  tff(c_470, plain, (~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_3') | ~v1_ordinal1(k3_tarski('#skF_3')) | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_461, c_28])).
% 2.76/1.43  tff(c_475, plain, (~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v1_ordinal1(k3_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_30, c_470])).
% 2.76/1.43  tff(c_476, plain, (~v1_ordinal1(k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_475])).
% 2.76/1.43  tff(c_479, plain, (~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_275, c_476])).
% 2.76/1.43  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_479])).
% 2.76/1.43  tff(c_487, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_475])).
% 2.76/1.43  tff(c_491, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_487])).
% 2.76/1.43  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_491])).
% 2.76/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.43  
% 2.76/1.43  Inference rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Ref     : 0
% 2.76/1.43  #Sup     : 101
% 2.76/1.43  #Fact    : 0
% 2.76/1.43  #Define  : 0
% 2.76/1.43  #Split   : 1
% 2.76/1.43  #Chain   : 0
% 2.76/1.43  #Close   : 0
% 2.76/1.43  
% 2.76/1.43  Ordering : KBO
% 2.76/1.43  
% 2.76/1.43  Simplification rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Subsume      : 12
% 2.76/1.43  #Demod        : 4
% 2.76/1.43  #Tautology    : 4
% 2.76/1.43  #SimpNegUnit  : 0
% 2.76/1.43  #BackRed      : 0
% 2.76/1.43  
% 2.76/1.43  #Partial instantiations: 0
% 2.76/1.43  #Strategies tried      : 1
% 2.76/1.43  
% 2.76/1.43  Timing (in seconds)
% 2.76/1.43  ----------------------
% 2.76/1.44  Preprocessing        : 0.29
% 2.76/1.44  Parsing              : 0.17
% 2.76/1.44  CNF conversion       : 0.02
% 2.76/1.44  Main loop            : 0.36
% 2.76/1.44  Inferencing          : 0.16
% 2.76/1.44  Reduction            : 0.07
% 2.76/1.44  Demodulation         : 0.05
% 2.76/1.44  BG Simplification    : 0.02
% 2.76/1.44  Subsumption          : 0.09
% 2.76/1.44  Abstraction          : 0.01
% 2.76/1.44  MUC search           : 0.00
% 2.76/1.44  Cooper               : 0.00
% 2.76/1.44  Total                : 0.69
% 2.76/1.44  Index Insertion      : 0.00
% 2.76/1.44  Index Deletion       : 0.00
% 2.76/1.44  Index Matching       : 0.00
% 2.76/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
