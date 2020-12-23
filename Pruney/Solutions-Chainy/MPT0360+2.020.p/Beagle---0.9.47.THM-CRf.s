%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   75 (  91 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 179 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_74,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_17] : k3_tarski(k1_zfmisc_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k3_tarski(B_39))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [A_38,A_17] :
      ( r1_tarski(A_38,A_17)
      | ~ r2_hidden(A_38,k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_115,plain,(
    ! [B_48,A_17] :
      ( r1_tarski(B_48,A_17)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_108,c_91])).

tff(c_124,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_115])).

tff(c_136,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_253,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_301,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_2')
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_136,c_253])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_481,plain,(
    ! [A_99,A_100] :
      ( r1_tarski(A_99,'#skF_2')
      | ~ r1_tarski(A_99,A_100)
      | ~ r1_tarski(A_100,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_301,c_14])).

tff(c_501,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_481])).

tff(c_514,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_501])).

tff(c_34,plain,(
    ! [A_21] : k2_subset_1(A_21) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k2_subset_1(A_22),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_zfmisc_1(A_15),k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_246,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1558,plain,(
    ! [B_188,B_189,A_190] :
      ( r2_hidden(B_188,B_189)
      | ~ r1_tarski(A_190,B_189)
      | ~ m1_subset_1(B_188,A_190)
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_26,c_246])).

tff(c_1592,plain,(
    ! [B_188,B_16,A_15] :
      ( r2_hidden(B_188,k1_zfmisc_1(B_16))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_1558])).

tff(c_3013,plain,(
    ! [B_251,B_252,A_253] :
      ( r2_hidden(B_251,k1_zfmisc_1(B_252))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(A_253))
      | ~ r1_tarski(A_253,B_252) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1592])).

tff(c_3204,plain,(
    ! [A_258,B_259] :
      ( r2_hidden(A_258,k1_zfmisc_1(B_259))
      | ~ r1_tarski(A_258,B_259) ) ),
    inference(resolution,[status(thm)],[c_55,c_3013])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ r2_hidden(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3277,plain,(
    ! [A_258,B_259] :
      ( m1_subset_1(A_258,k1_zfmisc_1(B_259))
      | v1_xboole_0(k1_zfmisc_1(B_259))
      | ~ r1_tarski(A_258,B_259) ) ),
    inference(resolution,[status(thm)],[c_3204,c_24])).

tff(c_3309,plain,(
    ! [A_258,B_259] :
      ( m1_subset_1(A_258,k1_zfmisc_1(B_259))
      | ~ r1_tarski(A_258,B_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3277])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_725,plain,(
    ! [A_115,C_116,B_117] :
      ( r1_tarski(k3_subset_1(A_115,C_116),k3_subset_1(A_115,B_117))
      | ~ r1_tarski(B_117,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2526,plain,(
    ! [A_222,A_223,B_224,C_225] :
      ( r1_tarski(A_222,k3_subset_1(A_223,B_224))
      | ~ r1_tarski(A_222,k3_subset_1(A_223,C_225))
      | ~ r1_tarski(B_224,C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(A_223))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(A_223)) ) ),
    inference(resolution,[status(thm)],[c_725,c_14])).

tff(c_2542,plain,(
    ! [B_224] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_2',B_224))
      | ~ r1_tarski(B_224,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_224,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_2526])).

tff(c_5426,plain,(
    ! [B_313] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_2',B_313))
      | ~ r1_tarski(B_313,'#skF_4')
      | ~ m1_subset_1(B_313,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2542])).

tff(c_32,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k1_subset_1(A_28) = B_29
      | ~ r1_tarski(B_29,k3_subset_1(A_28,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( k1_xboole_0 = B_29
      | ~ r1_tarski(B_29,k3_subset_1(A_28,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46])).

tff(c_5453,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5426,c_56])).

tff(c_5481,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5453])).

tff(c_5482,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5481])).

tff(c_5492,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3309,c_5482])).

tff(c_5500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_5492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.24  
% 6.06/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.24  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.06/2.24  
% 6.06/2.24  %Foreground sorts:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Background operators:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Foreground operators:
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.06/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.06/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.24  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.06/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.06/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.06/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.24  
% 6.06/2.26  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.06/2.26  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 6.06/2.26  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.06/2.26  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.06/2.26  tff(f_59, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 6.06/2.26  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.06/2.26  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.06/2.26  tff(f_76, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.06/2.26  tff(f_78, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.06/2.26  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 6.06/2.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.06/2.26  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 6.06/2.26  tff(f_74, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.06/2.26  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 6.06/2.26  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.06/2.26  tff(c_52, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.26  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.26  tff(c_38, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.06/2.26  tff(c_108, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.06/2.26  tff(c_22, plain, (![A_17]: (k3_tarski(k1_zfmisc_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.06/2.26  tff(c_88, plain, (![A_38, B_39]: (r1_tarski(A_38, k3_tarski(B_39)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.06/2.26  tff(c_91, plain, (![A_38, A_17]: (r1_tarski(A_38, A_17) | ~r2_hidden(A_38, k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 6.06/2.26  tff(c_115, plain, (![B_48, A_17]: (r1_tarski(B_48, A_17) | ~m1_subset_1(B_48, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_108, c_91])).
% 6.06/2.26  tff(c_124, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_38, c_115])).
% 6.06/2.26  tff(c_136, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_124])).
% 6.06/2.26  tff(c_253, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.06/2.26  tff(c_301, plain, (![A_75]: (r1_tarski(A_75, '#skF_2') | ~r1_tarski(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_136, c_253])).
% 6.06/2.26  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.06/2.26  tff(c_481, plain, (![A_99, A_100]: (r1_tarski(A_99, '#skF_2') | ~r1_tarski(A_99, A_100) | ~r1_tarski(A_100, '#skF_4'))), inference(resolution, [status(thm)], [c_301, c_14])).
% 6.06/2.26  tff(c_501, plain, (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_481])).
% 6.06/2.26  tff(c_514, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_501])).
% 6.06/2.26  tff(c_34, plain, (![A_21]: (k2_subset_1(A_21)=A_21)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.06/2.26  tff(c_36, plain, (![A_22]: (m1_subset_1(k2_subset_1(A_22), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.06/2.26  tff(c_55, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 6.06/2.26  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k1_zfmisc_1(A_15), k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.06/2.26  tff(c_26, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.06/2.26  tff(c_246, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.06/2.26  tff(c_1558, plain, (![B_188, B_189, A_190]: (r2_hidden(B_188, B_189) | ~r1_tarski(A_190, B_189) | ~m1_subset_1(B_188, A_190) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_26, c_246])).
% 6.06/2.26  tff(c_1592, plain, (![B_188, B_16, A_15]: (r2_hidden(B_188, k1_zfmisc_1(B_16)) | ~m1_subset_1(B_188, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_20, c_1558])).
% 6.06/2.26  tff(c_3013, plain, (![B_251, B_252, A_253]: (r2_hidden(B_251, k1_zfmisc_1(B_252)) | ~m1_subset_1(B_251, k1_zfmisc_1(A_253)) | ~r1_tarski(A_253, B_252))), inference(negUnitSimplification, [status(thm)], [c_38, c_1592])).
% 6.06/2.26  tff(c_3204, plain, (![A_258, B_259]: (r2_hidden(A_258, k1_zfmisc_1(B_259)) | ~r1_tarski(A_258, B_259))), inference(resolution, [status(thm)], [c_55, c_3013])).
% 6.06/2.26  tff(c_24, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~r2_hidden(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.06/2.26  tff(c_3277, plain, (![A_258, B_259]: (m1_subset_1(A_258, k1_zfmisc_1(B_259)) | v1_xboole_0(k1_zfmisc_1(B_259)) | ~r1_tarski(A_258, B_259))), inference(resolution, [status(thm)], [c_3204, c_24])).
% 6.06/2.26  tff(c_3309, plain, (![A_258, B_259]: (m1_subset_1(A_258, k1_zfmisc_1(B_259)) | ~r1_tarski(A_258, B_259))), inference(negUnitSimplification, [status(thm)], [c_38, c_3277])).
% 6.06/2.26  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.26  tff(c_50, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.26  tff(c_725, plain, (![A_115, C_116, B_117]: (r1_tarski(k3_subset_1(A_115, C_116), k3_subset_1(A_115, B_117)) | ~r1_tarski(B_117, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_115)) | ~m1_subset_1(B_117, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.06/2.26  tff(c_2526, plain, (![A_222, A_223, B_224, C_225]: (r1_tarski(A_222, k3_subset_1(A_223, B_224)) | ~r1_tarski(A_222, k3_subset_1(A_223, C_225)) | ~r1_tarski(B_224, C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(A_223)) | ~m1_subset_1(B_224, k1_zfmisc_1(A_223)))), inference(resolution, [status(thm)], [c_725, c_14])).
% 6.06/2.26  tff(c_2542, plain, (![B_224]: (r1_tarski('#skF_3', k3_subset_1('#skF_2', B_224)) | ~r1_tarski(B_224, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_224, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_2526])).
% 6.06/2.26  tff(c_5426, plain, (![B_313]: (r1_tarski('#skF_3', k3_subset_1('#skF_2', B_313)) | ~r1_tarski(B_313, '#skF_4') | ~m1_subset_1(B_313, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2542])).
% 6.06/2.26  tff(c_32, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.06/2.26  tff(c_46, plain, (![A_28, B_29]: (k1_subset_1(A_28)=B_29 | ~r1_tarski(B_29, k3_subset_1(A_28, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.06/2.26  tff(c_56, plain, (![B_29, A_28]: (k1_xboole_0=B_29 | ~r1_tarski(B_29, k3_subset_1(A_28, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46])).
% 6.06/2.26  tff(c_5453, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_5426, c_56])).
% 6.06/2.26  tff(c_5481, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5453])).
% 6.06/2.26  tff(c_5482, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_5481])).
% 6.06/2.26  tff(c_5492, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3309, c_5482])).
% 6.06/2.26  tff(c_5500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_5492])).
% 6.06/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.26  
% 6.06/2.26  Inference rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Ref     : 0
% 6.06/2.26  #Sup     : 1255
% 6.06/2.26  #Fact    : 0
% 6.06/2.26  #Define  : 0
% 6.06/2.26  #Split   : 18
% 6.06/2.26  #Chain   : 0
% 6.06/2.26  #Close   : 0
% 6.06/2.26  
% 6.06/2.26  Ordering : KBO
% 6.06/2.26  
% 6.06/2.26  Simplification rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Subsume      : 578
% 6.06/2.26  #Demod        : 234
% 6.06/2.26  #Tautology    : 141
% 6.06/2.26  #SimpNegUnit  : 81
% 6.06/2.26  #BackRed      : 4
% 6.06/2.26  
% 6.06/2.26  #Partial instantiations: 0
% 6.06/2.26  #Strategies tried      : 1
% 6.06/2.26  
% 6.06/2.26  Timing (in seconds)
% 6.06/2.26  ----------------------
% 6.06/2.26  Preprocessing        : 0.31
% 6.06/2.26  Parsing              : 0.17
% 6.06/2.26  CNF conversion       : 0.02
% 6.06/2.26  Main loop            : 1.13
% 6.06/2.26  Inferencing          : 0.33
% 6.06/2.26  Reduction            : 0.31
% 6.06/2.26  Demodulation         : 0.19
% 6.06/2.26  BG Simplification    : 0.03
% 6.06/2.26  Subsumption          : 0.37
% 6.06/2.26  Abstraction          : 0.04
% 6.06/2.26  MUC search           : 0.00
% 6.06/2.26  Cooper               : 0.00
% 6.06/2.26  Total                : 1.47
% 6.06/2.26  Index Insertion      : 0.00
% 6.06/2.26  Index Deletion       : 0.00
% 6.06/2.26  Index Matching       : 0.00
% 6.06/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
