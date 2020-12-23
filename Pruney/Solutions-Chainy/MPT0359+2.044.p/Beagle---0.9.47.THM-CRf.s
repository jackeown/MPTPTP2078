%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 126 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 174 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = k2_subset_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_44])).

tff(c_60,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_xboole_0) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59])).

tff(c_46,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_158,plain,(
    ! [A_24] : k3_subset_1(A_24,k3_subset_1(A_24,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_154])).

tff(c_161,plain,(
    ! [A_24] : k3_subset_1(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_158])).

tff(c_50,plain,
    ( k2_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,
    ( '#skF_5' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_90,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | k2_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_57,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_91,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_57])).

tff(c_92,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_90])).

tff(c_162,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_92])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_162])).

tff(c_166,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_167,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_226,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_229,plain,(
    ! [A_1,B_2,B_67] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_67)
      | ~ r1_tarski(A_1,B_67)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_208,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),A_61)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_452,plain,(
    ! [A_98,B_99,B_100] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_98,B_99),B_100),B_99)
      | r1_tarski(k4_xboole_0(A_98,B_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_208,c_10])).

tff(c_467,plain,(
    ! [B_100] :
      ( ~ r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),B_100),'#skF_5')
      | r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_452])).

tff(c_488,plain,(
    ! [B_103] :
      ( ~ r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),B_103),'#skF_5')
      | r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_467])).

tff(c_492,plain,(
    ! [B_2] :
      ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_5')
      | r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_229,c_488])).

tff(c_500,plain,(
    ! [B_104] : r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_492])).

tff(c_170,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_182,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_512,plain,(
    k3_subset_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_500,c_182])).

tff(c_283,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_290,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_283])).

tff(c_517,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_290])).

tff(c_523,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_517])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.68/1.37  
% 2.68/1.37  %Foreground sorts:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Background operators:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Foreground operators:
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.37  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.68/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.68/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.37  
% 2.68/1.39  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.68/1.39  tff(f_54, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.68/1.39  tff(f_56, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.68/1.39  tff(f_66, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.68/1.39  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.39  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.68/1.39  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.68/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.68/1.39  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.68/1.39  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.68/1.39  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.39  tff(c_34, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.39  tff(c_36, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.39  tff(c_38, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.39  tff(c_44, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=k2_subset_1(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.68/1.39  tff(c_59, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_44])).
% 2.68/1.39  tff(c_60, plain, (![A_23]: (k3_subset_1(A_23, k1_xboole_0)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59])).
% 2.68/1.39  tff(c_46, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.39  tff(c_154, plain, (![A_49, B_50]: (k3_subset_1(A_49, k3_subset_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.39  tff(c_158, plain, (![A_24]: (k3_subset_1(A_24, k3_subset_1(A_24, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_154])).
% 2.68/1.39  tff(c_161, plain, (![A_24]: (k3_subset_1(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_158])).
% 2.68/1.39  tff(c_50, plain, (k2_subset_1('#skF_4')!='#skF_5' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.39  tff(c_58, plain, ('#skF_5'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.68/1.39  tff(c_90, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 2.68/1.39  tff(c_56, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | k2_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.39  tff(c_57, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 2.68/1.39  tff(c_91, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_57])).
% 2.68/1.39  tff(c_92, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_90])).
% 2.68/1.39  tff(c_162, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_92])).
% 2.68/1.39  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_162])).
% 2.68/1.39  tff(c_166, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 2.68/1.39  tff(c_167, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 2.68/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.39  tff(c_226, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.39  tff(c_229, plain, (![A_1, B_2, B_67]: (r2_hidden('#skF_1'(A_1, B_2), B_67) | ~r1_tarski(A_1, B_67) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_226])).
% 2.68/1.39  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.68/1.39  tff(c_230, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.39  tff(c_239, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_230])).
% 2.68/1.39  tff(c_208, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), A_61) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.39  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.39  tff(c_452, plain, (![A_98, B_99, B_100]: (~r2_hidden('#skF_1'(k4_xboole_0(A_98, B_99), B_100), B_99) | r1_tarski(k4_xboole_0(A_98, B_99), B_100))), inference(resolution, [status(thm)], [c_208, c_10])).
% 2.68/1.39  tff(c_467, plain, (![B_100]: (~r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), B_100), '#skF_5') | r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_100))), inference(superposition, [status(thm), theory('equality')], [c_239, c_452])).
% 2.68/1.39  tff(c_488, plain, (![B_103]: (~r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), B_103), '#skF_5') | r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_103))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_467])).
% 2.68/1.39  tff(c_492, plain, (![B_2]: (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_5') | r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_2))), inference(resolution, [status(thm)], [c_229, c_488])).
% 2.68/1.39  tff(c_500, plain, (![B_104]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_104))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_492])).
% 2.68/1.39  tff(c_170, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.39  tff(c_182, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_170])).
% 2.68/1.39  tff(c_512, plain, (k3_subset_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_500, c_182])).
% 2.68/1.39  tff(c_283, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.39  tff(c_290, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_48, c_283])).
% 2.68/1.39  tff(c_517, plain, (k3_subset_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_512, c_290])).
% 2.68/1.39  tff(c_523, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_517])).
% 2.68/1.39  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_523])).
% 2.68/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  Inference rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Ref     : 0
% 2.68/1.39  #Sup     : 94
% 2.68/1.39  #Fact    : 0
% 2.68/1.39  #Define  : 0
% 2.68/1.39  #Split   : 3
% 2.68/1.39  #Chain   : 0
% 2.68/1.39  #Close   : 0
% 2.68/1.39  
% 2.68/1.39  Ordering : KBO
% 2.68/1.39  
% 2.68/1.39  Simplification rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Subsume      : 6
% 2.68/1.39  #Demod        : 40
% 2.68/1.39  #Tautology    : 51
% 2.68/1.39  #SimpNegUnit  : 3
% 2.68/1.39  #BackRed      : 11
% 2.68/1.39  
% 2.68/1.39  #Partial instantiations: 0
% 2.68/1.39  #Strategies tried      : 1
% 2.68/1.39  
% 2.68/1.39  Timing (in seconds)
% 2.68/1.39  ----------------------
% 2.68/1.40  Preprocessing        : 0.32
% 2.68/1.40  Parsing              : 0.16
% 2.68/1.40  CNF conversion       : 0.02
% 2.68/1.40  Main loop            : 0.29
% 2.68/1.40  Inferencing          : 0.10
% 2.68/1.40  Reduction            : 0.09
% 2.68/1.40  Demodulation         : 0.07
% 2.68/1.40  BG Simplification    : 0.02
% 2.68/1.40  Subsumption          : 0.06
% 2.68/1.40  Abstraction          : 0.02
% 2.68/1.40  MUC search           : 0.00
% 2.68/1.40  Cooper               : 0.00
% 2.68/1.40  Total                : 0.66
% 2.68/1.40  Index Insertion      : 0.00
% 2.68/1.40  Index Deletion       : 0.00
% 2.68/1.40  Index Matching       : 0.00
% 2.68/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
