%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 114 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 226 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(k1_tarski(A_10),B_11)
      | r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_345,plain,(
    ! [C_76,A_77,B_78] :
      ( k7_relat_1(k7_relat_1(C_76,A_77),B_78) = k1_xboole_0
      | ~ r1_xboole_0(A_77,B_78)
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_357,plain,(
    ! [C_76,A_77,B_78] :
      ( k9_relat_1(k7_relat_1(C_76,A_77),B_78) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(C_76,A_77))
      | ~ r1_xboole_0(A_77,B_78)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_20])).

tff(c_449,plain,(
    ! [C_95,A_96,B_97] :
      ( k9_relat_1(k7_relat_1(C_95,A_96),B_97) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(C_95,A_96))
      | ~ r1_xboole_0(A_96,B_97)
      | ~ v1_relat_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_357])).

tff(c_464,plain,(
    ! [A_99,B_100,B_101] :
      ( k9_relat_1(k7_relat_1(A_99,B_100),B_101) = k1_xboole_0
      | ~ r1_xboole_0(B_100,B_101)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_18,c_449])).

tff(c_34,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_287,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(k7_relat_1(B_67,A_68)) = k9_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_302,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_287])).

tff(c_5773,plain,(
    ! [A_366,B_367] :
      ( k2_relat_1(k7_relat_1(A_366,B_367)) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_366,B_367))
      | ~ v1_relat_1(k7_relat_1(A_366,B_367))
      | ~ r1_xboole_0(B_367,k1_relat_1(k7_relat_1(A_366,B_367)))
      | ~ v1_relat_1(A_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_302])).

tff(c_9889,plain,(
    ! [A_439,A_440] :
      ( k2_relat_1(k7_relat_1(A_439,k1_tarski(A_440))) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_439,k1_tarski(A_440)))
      | ~ v1_relat_1(A_439)
      | r2_hidden(A_440,k1_relat_1(k7_relat_1(A_439,k1_tarski(A_440)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_5773])).

tff(c_30,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(A_19,k1_relat_1(k7_relat_1(C_21,B_20)))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9933,plain,(
    ! [A_441,A_442] :
      ( r2_hidden(A_441,k1_relat_1(A_442))
      | k2_relat_1(k7_relat_1(A_442,k1_tarski(A_441))) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_442,k1_tarski(A_441)))
      | ~ v1_relat_1(A_442) ) ),
    inference(resolution,[status(thm)],[c_9889,c_30])).

tff(c_9960,plain,(
    ! [A_443,A_444] :
      ( r2_hidden(A_443,k1_relat_1(A_444))
      | k2_relat_1(k7_relat_1(A_444,k1_tarski(A_443))) = k1_xboole_0
      | ~ v1_relat_1(A_444) ) ),
    inference(resolution,[status(thm)],[c_18,c_9933])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9973,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9960,c_38])).

tff(c_10002,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_9973])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_430,plain,(
    ! [C_92,A_93,B_94] :
      ( k2_tarski(k1_funct_1(C_92,A_93),k1_funct_1(C_92,B_94)) = k9_relat_1(C_92,k2_tarski(A_93,B_94))
      | ~ r2_hidden(B_94,k1_relat_1(C_92))
      | ~ r2_hidden(A_93,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_444,plain,(
    ! [C_92,A_93] :
      ( k9_relat_1(C_92,k2_tarski(A_93,A_93)) = k1_tarski(k1_funct_1(C_92,A_93))
      | ~ r2_hidden(A_93,k1_relat_1(C_92))
      | ~ r2_hidden(A_93,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_430])).

tff(c_448,plain,(
    ! [C_92,A_93] :
      ( k9_relat_1(C_92,k1_tarski(A_93)) = k1_tarski(k1_funct_1(C_92,A_93))
      | ~ r2_hidden(A_93,k1_relat_1(C_92))
      | ~ r2_hidden(A_93,k1_relat_1(C_92))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_444])).

tff(c_10020,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10002,c_448])).

tff(c_10030,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_10002,c_10020])).

tff(c_293,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_38])).

tff(c_305,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_293])).

tff(c_10031,plain,(
    ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10030,c_305])).

tff(c_10034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.71  
% 8.24/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.71  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.24/2.71  
% 8.24/2.71  %Foreground sorts:
% 8.24/2.71  
% 8.24/2.71  
% 8.24/2.71  %Background operators:
% 8.24/2.71  
% 8.24/2.71  
% 8.24/2.71  %Foreground operators:
% 8.24/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.24/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.24/2.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.24/2.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.24/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.24/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/2.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.24/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.24/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.24/2.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.24/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.24/2.71  tff('#skF_2', type, '#skF_2': $i).
% 8.24/2.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.24/2.71  tff('#skF_1', type, '#skF_1': $i).
% 8.24/2.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.24/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.24/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.24/2.71  
% 8.24/2.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.24/2.73  tff(f_90, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 8.24/2.73  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.24/2.73  tff(f_48, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.24/2.73  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.24/2.73  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.24/2.73  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 8.24/2.73  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.24/2.73  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 8.24/2.73  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 8.24/2.73  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.24/2.73  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 8.24/2.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.24/2.73  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.73  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.73  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.24/2.73  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.24/2.73  tff(c_16, plain, (![A_10, B_11]: (r1_xboole_0(k1_tarski(A_10), B_11) | r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.24/2.73  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.24/2.73  tff(c_345, plain, (![C_76, A_77, B_78]: (k7_relat_1(k7_relat_1(C_76, A_77), B_78)=k1_xboole_0 | ~r1_xboole_0(A_77, B_78) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.24/2.73  tff(c_20, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.24/2.73  tff(c_357, plain, (![C_76, A_77, B_78]: (k9_relat_1(k7_relat_1(C_76, A_77), B_78)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k7_relat_1(C_76, A_77)) | ~r1_xboole_0(A_77, B_78) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_345, c_20])).
% 8.24/2.73  tff(c_449, plain, (![C_95, A_96, B_97]: (k9_relat_1(k7_relat_1(C_95, A_96), B_97)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(C_95, A_96)) | ~r1_xboole_0(A_96, B_97) | ~v1_relat_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_357])).
% 8.24/2.73  tff(c_464, plain, (![A_99, B_100, B_101]: (k9_relat_1(k7_relat_1(A_99, B_100), B_101)=k1_xboole_0 | ~r1_xboole_0(B_100, B_101) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_18, c_449])).
% 8.24/2.73  tff(c_34, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.24/2.73  tff(c_287, plain, (![B_67, A_68]: (k2_relat_1(k7_relat_1(B_67, A_68))=k9_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.24/2.73  tff(c_302, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_34, c_287])).
% 8.24/2.73  tff(c_5773, plain, (![A_366, B_367]: (k2_relat_1(k7_relat_1(A_366, B_367))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_366, B_367)) | ~v1_relat_1(k7_relat_1(A_366, B_367)) | ~r1_xboole_0(B_367, k1_relat_1(k7_relat_1(A_366, B_367))) | ~v1_relat_1(A_366))), inference(superposition, [status(thm), theory('equality')], [c_464, c_302])).
% 8.24/2.73  tff(c_9889, plain, (![A_439, A_440]: (k2_relat_1(k7_relat_1(A_439, k1_tarski(A_440)))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_439, k1_tarski(A_440))) | ~v1_relat_1(A_439) | r2_hidden(A_440, k1_relat_1(k7_relat_1(A_439, k1_tarski(A_440)))))), inference(resolution, [status(thm)], [c_16, c_5773])).
% 8.24/2.73  tff(c_30, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(A_19, k1_relat_1(k7_relat_1(C_21, B_20))) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.24/2.73  tff(c_9933, plain, (![A_441, A_442]: (r2_hidden(A_441, k1_relat_1(A_442)) | k2_relat_1(k7_relat_1(A_442, k1_tarski(A_441)))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_442, k1_tarski(A_441))) | ~v1_relat_1(A_442))), inference(resolution, [status(thm)], [c_9889, c_30])).
% 8.24/2.73  tff(c_9960, plain, (![A_443, A_444]: (r2_hidden(A_443, k1_relat_1(A_444)) | k2_relat_1(k7_relat_1(A_444, k1_tarski(A_443)))=k1_xboole_0 | ~v1_relat_1(A_444))), inference(resolution, [status(thm)], [c_18, c_9933])).
% 8.24/2.73  tff(c_38, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.73  tff(c_9973, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9960, c_38])).
% 8.24/2.73  tff(c_10002, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_9973])).
% 8.24/2.73  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.73  tff(c_430, plain, (![C_92, A_93, B_94]: (k2_tarski(k1_funct_1(C_92, A_93), k1_funct_1(C_92, B_94))=k9_relat_1(C_92, k2_tarski(A_93, B_94)) | ~r2_hidden(B_94, k1_relat_1(C_92)) | ~r2_hidden(A_93, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.24/2.73  tff(c_444, plain, (![C_92, A_93]: (k9_relat_1(C_92, k2_tarski(A_93, A_93))=k1_tarski(k1_funct_1(C_92, A_93)) | ~r2_hidden(A_93, k1_relat_1(C_92)) | ~r2_hidden(A_93, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(superposition, [status(thm), theory('equality')], [c_10, c_430])).
% 8.24/2.73  tff(c_448, plain, (![C_92, A_93]: (k9_relat_1(C_92, k1_tarski(A_93))=k1_tarski(k1_funct_1(C_92, A_93)) | ~r2_hidden(A_93, k1_relat_1(C_92)) | ~r2_hidden(A_93, k1_relat_1(C_92)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_444])).
% 8.24/2.73  tff(c_10020, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10002, c_448])).
% 8.24/2.73  tff(c_10030, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_10002, c_10020])).
% 8.24/2.73  tff(c_293, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_287, c_38])).
% 8.24/2.73  tff(c_305, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_293])).
% 8.24/2.73  tff(c_10031, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10030, c_305])).
% 8.24/2.73  tff(c_10034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10031])).
% 8.24/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.24/2.73  
% 8.24/2.73  Inference rules
% 8.24/2.73  ----------------------
% 8.24/2.73  #Ref     : 0
% 8.24/2.73  #Sup     : 2137
% 8.24/2.73  #Fact    : 24
% 8.24/2.73  #Define  : 0
% 8.24/2.73  #Split   : 18
% 8.24/2.73  #Chain   : 0
% 8.24/2.73  #Close   : 0
% 8.24/2.73  
% 8.24/2.73  Ordering : KBO
% 8.24/2.73  
% 8.24/2.73  Simplification rules
% 8.24/2.73  ----------------------
% 8.24/2.73  #Subsume      : 848
% 8.24/2.73  #Demod        : 2942
% 8.24/2.73  #Tautology    : 1091
% 8.24/2.73  #SimpNegUnit  : 19
% 8.24/2.73  #BackRed      : 29
% 8.24/2.73  
% 8.24/2.73  #Partial instantiations: 0
% 8.24/2.73  #Strategies tried      : 1
% 8.24/2.73  
% 8.24/2.73  Timing (in seconds)
% 8.24/2.73  ----------------------
% 8.24/2.73  Preprocessing        : 0.30
% 8.24/2.73  Parsing              : 0.16
% 8.24/2.73  CNF conversion       : 0.02
% 8.24/2.73  Main loop            : 1.66
% 8.24/2.73  Inferencing          : 0.48
% 8.24/2.73  Reduction            : 0.52
% 8.24/2.73  Demodulation         : 0.37
% 8.24/2.73  BG Simplification    : 0.05
% 8.24/2.73  Subsumption          : 0.50
% 8.24/2.73  Abstraction          : 0.08
% 8.24/2.73  MUC search           : 0.00
% 8.24/2.73  Cooper               : 0.00
% 8.24/2.73  Total                : 1.98
% 8.24/2.73  Index Insertion      : 0.00
% 8.24/2.73  Index Deletion       : 0.00
% 8.24/2.73  Index Matching       : 0.00
% 8.24/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
