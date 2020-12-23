%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 152 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_132,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | ~ m1_subset_1(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    ! [B_59,A_16] :
      ( r1_tarski(B_59,A_16)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_144,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_139])).

tff(c_160,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_144])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_204,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_220,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_204])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_400,plain,(
    ! [A_93] :
      ( r1_xboole_0(A_93,'#skF_5')
      | ~ r1_tarski(A_93,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_10])).

tff(c_422,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_222,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(A_80,k4_xboole_0(B_81,C_82))
      | ~ r1_xboole_0(A_80,C_82)
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_14,c_162])).

tff(c_226,plain,(
    ! [B_81,C_82] :
      ( k4_xboole_0(B_81,C_82) = B_81
      | ~ r1_xboole_0(B_81,C_82)
      | ~ r1_tarski(B_81,B_81) ) ),
    inference(resolution,[status(thm)],[c_222,c_179])).

tff(c_237,plain,(
    ! [B_81,C_82] :
      ( k4_xboole_0(B_81,C_82) = B_81
      | ~ r1_xboole_0(B_81,C_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_226])).

tff(c_430,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_422,c_237])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,k4_xboole_0(C_12,B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_482,plain,(
    ! [A_95] :
      ( r1_xboole_0(A_95,'#skF_4')
      | ~ r1_tarski(A_95,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_16])).

tff(c_509,plain,(
    ! [A_101] :
      ( k4_xboole_0(A_101,'#skF_4') = A_101
      | ~ r1_tarski(A_101,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_482,c_237])).

tff(c_529,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_509])).

tff(c_75,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_xboole_0(A_39,C_40)
      | ~ r1_tarski(A_39,k4_xboole_0(B_41,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [B_41,C_40] : r1_xboole_0(k4_xboole_0(B_41,C_40),C_40) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_585,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_85])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_221,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_204])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k4_xboole_0(B_14,C_15))
      | ~ r1_xboole_0(A_13,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5286,plain,(
    ! [A_209] :
      ( r1_tarski(A_209,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_209,'#skF_4')
      | ~ r1_tarski(A_209,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_18])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5317,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_5286,c_44])).

tff(c_5332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_585,c_5317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:23:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.08  
% 5.44/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.44/2.08  
% 5.44/2.08  %Foreground sorts:
% 5.44/2.08  
% 5.44/2.08  
% 5.44/2.08  %Background operators:
% 5.44/2.08  
% 5.44/2.08  
% 5.44/2.08  %Foreground operators:
% 5.44/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.44/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.44/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.44/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.44/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.44/2.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.44/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.44/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.44/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.44/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.44/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.44/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.44/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.44/2.08  
% 5.44/2.09  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 5.44/2.09  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.44/2.09  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.44/2.09  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.44/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.44/2.09  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.44/2.09  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.44/2.09  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.44/2.09  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.44/2.09  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.44/2.09  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.44/2.09  tff(c_42, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.44/2.09  tff(c_132, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | ~m1_subset_1(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.44/2.09  tff(c_20, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.44/2.09  tff(c_139, plain, (![B_59, A_16]: (r1_tarski(B_59, A_16) | ~m1_subset_1(B_59, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_132, c_20])).
% 5.44/2.09  tff(c_144, plain, (![B_61, A_62]: (r1_tarski(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(negUnitSimplification, [status(thm)], [c_42, c_139])).
% 5.44/2.09  tff(c_160, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_144])).
% 5.44/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.09  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.44/2.09  tff(c_204, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.44/2.09  tff(c_220, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_204])).
% 5.44/2.09  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.44/2.09  tff(c_400, plain, (![A_93]: (r1_xboole_0(A_93, '#skF_5') | ~r1_tarski(A_93, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_220, c_10])).
% 5.44/2.09  tff(c_422, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_400])).
% 5.44/2.09  tff(c_222, plain, (![A_80, B_81, C_82]: (r1_tarski(A_80, k4_xboole_0(B_81, C_82)) | ~r1_xboole_0(A_80, C_82) | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.44/2.09  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.44/2.09  tff(c_162, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.09  tff(c_179, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_162])).
% 5.44/2.09  tff(c_226, plain, (![B_81, C_82]: (k4_xboole_0(B_81, C_82)=B_81 | ~r1_xboole_0(B_81, C_82) | ~r1_tarski(B_81, B_81))), inference(resolution, [status(thm)], [c_222, c_179])).
% 5.44/2.09  tff(c_237, plain, (![B_81, C_82]: (k4_xboole_0(B_81, C_82)=B_81 | ~r1_xboole_0(B_81, C_82))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_226])).
% 5.44/2.09  tff(c_430, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_422, c_237])).
% 5.44/2.09  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, k4_xboole_0(C_12, B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.44/2.09  tff(c_482, plain, (![A_95]: (r1_xboole_0(A_95, '#skF_4') | ~r1_tarski(A_95, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_16])).
% 5.44/2.09  tff(c_509, plain, (![A_101]: (k4_xboole_0(A_101, '#skF_4')=A_101 | ~r1_tarski(A_101, '#skF_5'))), inference(resolution, [status(thm)], [c_482, c_237])).
% 5.44/2.09  tff(c_529, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_509])).
% 5.44/2.09  tff(c_75, plain, (![A_39, C_40, B_41]: (r1_xboole_0(A_39, C_40) | ~r1_tarski(A_39, k4_xboole_0(B_41, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.44/2.09  tff(c_85, plain, (![B_41, C_40]: (r1_xboole_0(k4_xboole_0(B_41, C_40), C_40))), inference(resolution, [status(thm)], [c_6, c_75])).
% 5.44/2.09  tff(c_585, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_529, c_85])).
% 5.44/2.09  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.44/2.09  tff(c_221, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_204])).
% 5.44/2.09  tff(c_18, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k4_xboole_0(B_14, C_15)) | ~r1_xboole_0(A_13, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.44/2.09  tff(c_5286, plain, (![A_209]: (r1_tarski(A_209, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_209, '#skF_4') | ~r1_tarski(A_209, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_18])).
% 5.44/2.09  tff(c_44, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.44/2.09  tff(c_5317, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_5286, c_44])).
% 5.44/2.09  tff(c_5332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_585, c_5317])).
% 5.44/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.09  
% 5.44/2.09  Inference rules
% 5.44/2.09  ----------------------
% 5.44/2.09  #Ref     : 0
% 5.44/2.09  #Sup     : 1226
% 5.44/2.09  #Fact    : 0
% 5.44/2.09  #Define  : 0
% 5.44/2.09  #Split   : 5
% 5.44/2.09  #Chain   : 0
% 5.44/2.09  #Close   : 0
% 5.44/2.09  
% 5.44/2.09  Ordering : KBO
% 5.44/2.09  
% 5.44/2.09  Simplification rules
% 5.44/2.09  ----------------------
% 5.44/2.09  #Subsume      : 140
% 5.44/2.09  #Demod        : 798
% 5.44/2.09  #Tautology    : 519
% 5.44/2.09  #SimpNegUnit  : 7
% 5.44/2.09  #BackRed      : 0
% 5.44/2.09  
% 5.44/2.09  #Partial instantiations: 0
% 5.44/2.09  #Strategies tried      : 1
% 5.44/2.09  
% 5.44/2.09  Timing (in seconds)
% 5.44/2.09  ----------------------
% 5.44/2.10  Preprocessing        : 0.29
% 5.44/2.10  Parsing              : 0.15
% 5.44/2.10  CNF conversion       : 0.02
% 5.44/2.10  Main loop            : 1.01
% 5.44/2.10  Inferencing          : 0.31
% 5.44/2.10  Reduction            : 0.40
% 5.44/2.10  Demodulation         : 0.30
% 5.44/2.10  BG Simplification    : 0.04
% 5.44/2.10  Subsumption          : 0.20
% 5.44/2.10  Abstraction          : 0.05
% 5.44/2.10  MUC search           : 0.00
% 5.44/2.10  Cooper               : 0.00
% 5.44/2.10  Total                : 1.33
% 5.44/2.10  Index Insertion      : 0.00
% 5.44/2.10  Index Deletion       : 0.00
% 5.44/2.10  Index Matching       : 0.00
% 5.44/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
