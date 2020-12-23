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
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   56 (  60 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 (  89 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_60,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_22] : m1_subset_1('#skF_2'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_18,B_19] : ~ v1_xboole_0(k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_45,C_46] :
      ( ~ r1_xboole_0(A_45,A_45)
      | ~ r2_hidden(C_46,A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_88,plain,(
    ! [C_47,A_48] :
      ( ~ r2_hidden(C_47,k1_tarski(A_48))
      | r2_hidden(A_48,k1_tarski(A_48)) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_91,plain,(
    ! [A_48,A_24] :
      ( r2_hidden(A_48,k1_tarski(A_48))
      | v1_xboole_0(k1_tarski(A_48))
      | ~ m1_subset_1(A_24,k1_tarski(A_48)) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_95,plain,(
    ! [A_49,A_50] :
      ( r2_hidden(A_49,k1_tarski(A_49))
      | ~ m1_subset_1(A_50,k1_tarski(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_91])).

tff(c_98,plain,(
    ! [A_49] : r2_hidden(A_49,k1_tarski(A_49)) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_146,plain,(
    ! [D_64,C_65,B_66,A_67] :
      ( r2_hidden(k1_funct_1(D_64,C_65),B_66)
      | k1_xboole_0 = B_66
      | ~ r2_hidden(C_65,A_67)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66)))
      | ~ v1_funct_2(D_64,A_67,B_66)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(k1_funct_1(D_74,A_75),B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_75),B_76)))
      | ~ v1_funct_2(D_74,k1_tarski(A_75),B_76)
      | ~ v1_funct_1(D_74) ) ),
    inference(resolution,[status(thm)],[c_98,c_146])).

tff(c_187,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_184])).

tff(c_194,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_187])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.30  
% 1.86/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.30  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.86/1.30  
% 1.86/1.30  %Foreground sorts:
% 1.86/1.30  
% 1.86/1.30  
% 1.86/1.30  %Background operators:
% 1.86/1.30  
% 1.86/1.30  
% 1.86/1.30  %Foreground operators:
% 1.86/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.86/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.86/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.30  
% 1.86/1.32  tff(f_90, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 1.86/1.32  tff(f_60, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.86/1.32  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.86/1.32  tff(f_52, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 1.86/1.32  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.86/1.32  tff(f_57, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.86/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.86/1.32  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.32  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.86/1.32  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.86/1.32  tff(c_26, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.86/1.32  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.86/1.32  tff(c_32, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.86/1.32  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.86/1.32  tff(c_20, plain, (![A_22]: (m1_subset_1('#skF_2'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.32  tff(c_46, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.32  tff(c_16, plain, (![A_18, B_19]: (~v1_xboole_0(k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.32  tff(c_51, plain, (![A_34]: (~v1_xboole_0(k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_16])).
% 1.86/1.32  tff(c_22, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | v1_xboole_0(B_25) | ~m1_subset_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.32  tff(c_18, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.32  tff(c_74, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.32  tff(c_83, plain, (![A_45, C_46]: (~r1_xboole_0(A_45, A_45) | ~r2_hidden(C_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_2, c_74])).
% 1.86/1.32  tff(c_88, plain, (![C_47, A_48]: (~r2_hidden(C_47, k1_tarski(A_48)) | r2_hidden(A_48, k1_tarski(A_48)))), inference(resolution, [status(thm)], [c_18, c_83])).
% 1.86/1.32  tff(c_91, plain, (![A_48, A_24]: (r2_hidden(A_48, k1_tarski(A_48)) | v1_xboole_0(k1_tarski(A_48)) | ~m1_subset_1(A_24, k1_tarski(A_48)))), inference(resolution, [status(thm)], [c_22, c_88])).
% 1.86/1.32  tff(c_95, plain, (![A_49, A_50]: (r2_hidden(A_49, k1_tarski(A_49)) | ~m1_subset_1(A_50, k1_tarski(A_49)))), inference(negUnitSimplification, [status(thm)], [c_51, c_91])).
% 1.86/1.32  tff(c_98, plain, (![A_49]: (r2_hidden(A_49, k1_tarski(A_49)))), inference(resolution, [status(thm)], [c_20, c_95])).
% 1.86/1.32  tff(c_146, plain, (![D_64, C_65, B_66, A_67]: (r2_hidden(k1_funct_1(D_64, C_65), B_66) | k1_xboole_0=B_66 | ~r2_hidden(C_65, A_67) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))) | ~v1_funct_2(D_64, A_67, B_66) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.86/1.32  tff(c_184, plain, (![D_74, A_75, B_76]: (r2_hidden(k1_funct_1(D_74, A_75), B_76) | k1_xboole_0=B_76 | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_75), B_76))) | ~v1_funct_2(D_74, k1_tarski(A_75), B_76) | ~v1_funct_1(D_74))), inference(resolution, [status(thm)], [c_98, c_146])).
% 1.86/1.32  tff(c_187, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_184])).
% 1.86/1.32  tff(c_194, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_187])).
% 1.86/1.32  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_194])).
% 1.86/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.32  
% 1.86/1.32  Inference rules
% 1.86/1.32  ----------------------
% 1.86/1.32  #Ref     : 0
% 1.86/1.32  #Sup     : 34
% 1.86/1.32  #Fact    : 0
% 1.86/1.32  #Define  : 0
% 1.86/1.32  #Split   : 1
% 1.86/1.32  #Chain   : 0
% 1.86/1.32  #Close   : 0
% 1.86/1.32  
% 1.86/1.32  Ordering : KBO
% 1.86/1.32  
% 1.86/1.32  Simplification rules
% 1.86/1.32  ----------------------
% 1.86/1.32  #Subsume      : 3
% 1.86/1.32  #Demod        : 8
% 1.86/1.32  #Tautology    : 16
% 1.86/1.32  #SimpNegUnit  : 3
% 1.86/1.32  #BackRed      : 0
% 1.86/1.32  
% 1.86/1.32  #Partial instantiations: 0
% 1.86/1.32  #Strategies tried      : 1
% 1.86/1.32  
% 1.86/1.32  Timing (in seconds)
% 1.86/1.32  ----------------------
% 1.86/1.32  Preprocessing        : 0.30
% 1.86/1.32  Parsing              : 0.16
% 1.86/1.32  CNF conversion       : 0.02
% 1.86/1.32  Main loop            : 0.16
% 1.86/1.32  Inferencing          : 0.07
% 1.86/1.32  Reduction            : 0.05
% 1.86/1.32  Demodulation         : 0.03
% 1.86/1.32  BG Simplification    : 0.01
% 1.86/1.32  Subsumption          : 0.02
% 1.86/1.32  Abstraction          : 0.01
% 1.86/1.32  MUC search           : 0.00
% 1.86/1.32  Cooper               : 0.00
% 1.86/1.32  Total                : 0.49
% 1.86/1.32  Index Insertion      : 0.00
% 1.86/1.32  Index Deletion       : 0.00
% 1.86/1.32  Index Matching       : 0.00
% 1.86/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
