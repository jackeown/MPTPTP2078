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
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_49,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_34,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_26] :
      ( v3_ordinal1(k1_ordinal1(A_26))
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35,plain,(
    ! [A_27] :
      ( v1_ordinal1(A_27)
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_35])).

tff(c_179,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),A_61)
      | r1_tarski(k3_tarski(A_61),B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_15,A_12] :
      ( r1_tarski(B_15,A_12)
      | ~ r2_hidden(B_15,A_12)
      | ~ v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_320,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),A_88)
      | ~ v1_ordinal1(A_88)
      | r1_tarski(k3_tarski(A_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_179,c_18])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( ~ r1_tarski('#skF_2'(A_8,B_9),B_9)
      | r1_tarski(k3_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_332,plain,(
    ! [A_90] :
      ( ~ v1_ordinal1(A_90)
      | r1_tarski(k3_tarski(A_90),A_90) ) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_22,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_3'(A_12),A_12)
      | v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_3'(A_66),B_67)
      | ~ r1_tarski(A_66,B_67)
      | v1_ordinal1(A_66) ) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_59,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,k3_tarski(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ r1_tarski('#skF_3'(A_12),A_12)
      | v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [B_36] :
      ( v1_ordinal1(k3_tarski(B_36))
      | ~ r2_hidden('#skF_3'(k3_tarski(B_36)),B_36) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_226,plain,(
    ! [B_67] :
      ( ~ r1_tarski(k3_tarski(B_67),B_67)
      | v1_ordinal1(k3_tarski(B_67)) ) ),
    inference(resolution,[status(thm)],[c_210,c_64])).

tff(c_341,plain,(
    ! [A_90] :
      ( v1_ordinal1(k3_tarski(A_90))
      | ~ v1_ordinal1(A_90) ) ),
    inference(resolution,[status(thm)],[c_332,c_226])).

tff(c_330,plain,(
    ! [A_88] :
      ( ~ v1_ordinal1(A_88)
      | r1_tarski(k3_tarski(A_88),A_88) ) ),
    inference(resolution,[status(thm)],[c_320,c_10])).

tff(c_24,plain,(
    ! [A_16] : r2_hidden(A_16,k1_ordinal1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,C_64)
      | ~ r2_hidden(B_65,C_64)
      | ~ r1_tarski(A_63,B_65)
      | ~ v3_ordinal1(C_64)
      | ~ v3_ordinal1(B_65)
      | ~ v1_ordinal1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_758,plain,(
    ! [A_130,A_131] :
      ( r2_hidden(A_130,k1_ordinal1(A_131))
      | ~ r1_tarski(A_130,A_131)
      | ~ v3_ordinal1(k1_ordinal1(A_131))
      | ~ v3_ordinal1(A_131)
      | ~ v1_ordinal1(A_130) ) ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( v3_ordinal1(A_24)
      | ~ r2_hidden(A_24,B_25)
      | ~ v3_ordinal1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1188,plain,(
    ! [A_164,A_165] :
      ( v3_ordinal1(A_164)
      | ~ r1_tarski(A_164,A_165)
      | ~ v3_ordinal1(k1_ordinal1(A_165))
      | ~ v3_ordinal1(A_165)
      | ~ v1_ordinal1(A_164) ) ),
    inference(resolution,[status(thm)],[c_758,c_28])).

tff(c_2975,plain,(
    ! [A_244] :
      ( v3_ordinal1(k3_tarski(A_244))
      | ~ v3_ordinal1(k1_ordinal1(A_244))
      | ~ v3_ordinal1(A_244)
      | ~ v1_ordinal1(k3_tarski(A_244))
      | ~ v1_ordinal1(A_244) ) ),
    inference(resolution,[status(thm)],[c_330,c_1188])).

tff(c_32,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3012,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2975,c_32])).

tff(c_3027,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_3012])).

tff(c_3028,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3027])).

tff(c_3031,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_341,c_3028])).

tff(c_3038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_3031])).

tff(c_3039,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3027])).

tff(c_3043,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_3039])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.86  
% 4.60/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.86  %$ r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.60/1.86  
% 4.60/1.86  %Foreground sorts:
% 4.60/1.86  
% 4.60/1.86  
% 4.60/1.86  %Background operators:
% 4.60/1.86  
% 4.60/1.86  
% 4.60/1.86  %Foreground operators:
% 4.60/1.86  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.86  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 4.60/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.86  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.60/1.86  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.60/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.86  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.60/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.60/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.60/1.86  
% 4.60/1.88  tff(f_87, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 4.60/1.88  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 4.60/1.88  tff(f_49, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.60/1.88  tff(f_43, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 4.60/1.88  tff(f_56, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.60/1.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.60/1.88  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.60/1.88  tff(f_58, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 4.60/1.88  tff(f_72, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 4.60/1.88  tff(f_78, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.60/1.88  tff(c_34, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.60/1.88  tff(c_30, plain, (![A_26]: (v3_ordinal1(k1_ordinal1(A_26)) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.60/1.88  tff(c_35, plain, (![A_27]: (v1_ordinal1(A_27) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.88  tff(c_39, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_35])).
% 4.60/1.88  tff(c_179, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), A_61) | r1_tarski(k3_tarski(A_61), B_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.88  tff(c_18, plain, (![B_15, A_12]: (r1_tarski(B_15, A_12) | ~r2_hidden(B_15, A_12) | ~v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.88  tff(c_320, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), A_88) | ~v1_ordinal1(A_88) | r1_tarski(k3_tarski(A_88), B_89))), inference(resolution, [status(thm)], [c_179, c_18])).
% 4.60/1.88  tff(c_10, plain, (![A_8, B_9]: (~r1_tarski('#skF_2'(A_8, B_9), B_9) | r1_tarski(k3_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.88  tff(c_332, plain, (![A_90]: (~v1_ordinal1(A_90) | r1_tarski(k3_tarski(A_90), A_90))), inference(resolution, [status(thm)], [c_320, c_10])).
% 4.60/1.88  tff(c_22, plain, (![A_12]: (r2_hidden('#skF_3'(A_12), A_12) | v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.88  tff(c_104, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.60/1.88  tff(c_210, plain, (![A_66, B_67]: (r2_hidden('#skF_3'(A_66), B_67) | ~r1_tarski(A_66, B_67) | v1_ordinal1(A_66))), inference(resolution, [status(thm)], [c_22, c_104])).
% 4.60/1.88  tff(c_59, plain, (![A_35, B_36]: (r1_tarski(A_35, k3_tarski(B_36)) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.60/1.88  tff(c_20, plain, (![A_12]: (~r1_tarski('#skF_3'(A_12), A_12) | v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.88  tff(c_64, plain, (![B_36]: (v1_ordinal1(k3_tarski(B_36)) | ~r2_hidden('#skF_3'(k3_tarski(B_36)), B_36))), inference(resolution, [status(thm)], [c_59, c_20])).
% 4.60/1.88  tff(c_226, plain, (![B_67]: (~r1_tarski(k3_tarski(B_67), B_67) | v1_ordinal1(k3_tarski(B_67)))), inference(resolution, [status(thm)], [c_210, c_64])).
% 4.60/1.88  tff(c_341, plain, (![A_90]: (v1_ordinal1(k3_tarski(A_90)) | ~v1_ordinal1(A_90))), inference(resolution, [status(thm)], [c_332, c_226])).
% 4.60/1.88  tff(c_330, plain, (![A_88]: (~v1_ordinal1(A_88) | r1_tarski(k3_tarski(A_88), A_88))), inference(resolution, [status(thm)], [c_320, c_10])).
% 4.60/1.88  tff(c_24, plain, (![A_16]: (r2_hidden(A_16, k1_ordinal1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.60/1.88  tff(c_191, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, C_64) | ~r2_hidden(B_65, C_64) | ~r1_tarski(A_63, B_65) | ~v3_ordinal1(C_64) | ~v3_ordinal1(B_65) | ~v1_ordinal1(A_63))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.88  tff(c_758, plain, (![A_130, A_131]: (r2_hidden(A_130, k1_ordinal1(A_131)) | ~r1_tarski(A_130, A_131) | ~v3_ordinal1(k1_ordinal1(A_131)) | ~v3_ordinal1(A_131) | ~v1_ordinal1(A_130))), inference(resolution, [status(thm)], [c_24, c_191])).
% 4.60/1.88  tff(c_28, plain, (![A_24, B_25]: (v3_ordinal1(A_24) | ~r2_hidden(A_24, B_25) | ~v3_ordinal1(B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.60/1.88  tff(c_1188, plain, (![A_164, A_165]: (v3_ordinal1(A_164) | ~r1_tarski(A_164, A_165) | ~v3_ordinal1(k1_ordinal1(A_165)) | ~v3_ordinal1(A_165) | ~v1_ordinal1(A_164))), inference(resolution, [status(thm)], [c_758, c_28])).
% 4.60/1.88  tff(c_2975, plain, (![A_244]: (v3_ordinal1(k3_tarski(A_244)) | ~v3_ordinal1(k1_ordinal1(A_244)) | ~v3_ordinal1(A_244) | ~v1_ordinal1(k3_tarski(A_244)) | ~v1_ordinal1(A_244))), inference(resolution, [status(thm)], [c_330, c_1188])).
% 4.60/1.88  tff(c_32, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.60/1.88  tff(c_3012, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2975, c_32])).
% 4.60/1.88  tff(c_3027, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v1_ordinal1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_34, c_3012])).
% 4.60/1.88  tff(c_3028, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_3027])).
% 4.60/1.88  tff(c_3031, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_341, c_3028])).
% 4.60/1.88  tff(c_3038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_3031])).
% 4.60/1.88  tff(c_3039, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_3027])).
% 4.60/1.88  tff(c_3043, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_3039])).
% 4.60/1.88  tff(c_3047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3043])).
% 4.60/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.88  
% 4.60/1.88  Inference rules
% 4.60/1.88  ----------------------
% 4.60/1.88  #Ref     : 0
% 4.60/1.88  #Sup     : 667
% 4.60/1.88  #Fact    : 0
% 4.60/1.88  #Define  : 0
% 4.60/1.88  #Split   : 1
% 4.60/1.88  #Chain   : 0
% 4.60/1.88  #Close   : 0
% 4.60/1.88  
% 4.60/1.88  Ordering : KBO
% 4.60/1.88  
% 4.60/1.88  Simplification rules
% 4.60/1.88  ----------------------
% 4.60/1.88  #Subsume      : 53
% 4.60/1.88  #Demod        : 31
% 4.60/1.88  #Tautology    : 25
% 4.60/1.88  #SimpNegUnit  : 0
% 4.60/1.88  #BackRed      : 0
% 4.60/1.88  
% 4.60/1.88  #Partial instantiations: 0
% 4.60/1.88  #Strategies tried      : 1
% 4.60/1.88  
% 4.60/1.88  Timing (in seconds)
% 4.60/1.88  ----------------------
% 4.60/1.88  Preprocessing        : 0.27
% 4.60/1.88  Parsing              : 0.15
% 4.60/1.88  CNF conversion       : 0.02
% 4.60/1.88  Main loop            : 0.80
% 4.60/1.88  Inferencing          : 0.28
% 4.60/1.88  Reduction            : 0.21
% 4.60/1.88  Demodulation         : 0.15
% 4.60/1.88  BG Simplification    : 0.03
% 4.60/1.88  Subsumption          : 0.22
% 4.60/1.88  Abstraction          : 0.03
% 4.60/1.88  MUC search           : 0.00
% 4.60/1.88  Cooper               : 0.00
% 4.60/1.88  Total                : 1.10
% 4.60/1.88  Index Insertion      : 0.00
% 4.60/1.88  Index Deletion       : 0.00
% 4.60/1.88  Index Matching       : 0.00
% 4.60/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
