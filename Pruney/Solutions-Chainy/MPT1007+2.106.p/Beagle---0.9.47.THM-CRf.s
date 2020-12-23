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
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  78 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [B_78,A_77,E_80,D_79,C_76] : k4_enumset1(A_77,A_77,B_78,C_76,D_79,E_80) = k3_enumset1(A_77,B_78,C_76,D_79,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [H_25,B_17,A_16,D_19,E_20,F_21] : r2_hidden(H_25,k4_enumset1(A_16,B_17,H_25,D_19,E_20,F_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_134,plain,(
    ! [E_83,D_85,A_81,C_84,B_82] : r2_hidden(B_82,k3_enumset1(A_81,B_82,C_84,D_85,E_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_20])).

tff(c_138,plain,(
    ! [A_86,B_87,C_88,D_89] : r2_hidden(A_86,k2_enumset1(A_86,B_87,C_88,D_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_142,plain,(
    ! [A_90,B_91,C_92] : r2_hidden(A_90,k1_enumset1(A_90,B_91,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_180,plain,(
    ! [A_100,B_101] : r2_hidden(A_100,k2_tarski(A_100,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_142])).

tff(c_183,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_180])).

tff(c_198,plain,(
    ! [D_117,C_118,B_119,A_120] :
      ( r2_hidden(k1_funct_1(D_117,C_118),B_119)
      | k1_xboole_0 = B_119
      | ~ r2_hidden(C_118,A_120)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(D_117,A_120,B_119)
      | ~ v1_funct_1(D_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_389,plain,(
    ! [D_188,A_189,B_190] :
      ( r2_hidden(k1_funct_1(D_188,A_189),B_190)
      | k1_xboole_0 = B_190
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_189),B_190)))
      | ~ v1_funct_2(D_188,k1_tarski(A_189),B_190)
      | ~ v1_funct_1(D_188) ) ),
    inference(resolution,[status(thm)],[c_183,c_198])).

tff(c_392,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_389])).

tff(c_395,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_392])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:49:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.41  
% 2.56/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.42  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.56/1.42  
% 2.56/1.42  %Foreground sorts:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Background operators:
% 2.56/1.42  
% 2.56/1.42  
% 2.56/1.42  %Foreground operators:
% 2.56/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.56/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.42  
% 2.56/1.43  tff(f_83, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.56/1.43  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.43  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.56/1.43  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.56/1.43  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.56/1.43  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.56/1.43  tff(f_59, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.56/1.43  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.56/1.43  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.43  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.43  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.43  tff(c_62, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.43  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.43  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.43  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.43  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.43  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.43  tff(c_107, plain, (![B_78, A_77, E_80, D_79, C_76]: (k4_enumset1(A_77, A_77, B_78, C_76, D_79, E_80)=k3_enumset1(A_77, B_78, C_76, D_79, E_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.43  tff(c_20, plain, (![H_25, B_17, A_16, D_19, E_20, F_21]: (r2_hidden(H_25, k4_enumset1(A_16, B_17, H_25, D_19, E_20, F_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.43  tff(c_134, plain, (![E_83, D_85, A_81, C_84, B_82]: (r2_hidden(B_82, k3_enumset1(A_81, B_82, C_84, D_85, E_83)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_20])).
% 2.56/1.43  tff(c_138, plain, (![A_86, B_87, C_88, D_89]: (r2_hidden(A_86, k2_enumset1(A_86, B_87, C_88, D_89)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_134])).
% 2.56/1.43  tff(c_142, plain, (![A_90, B_91, C_92]: (r2_hidden(A_90, k1_enumset1(A_90, B_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_138])).
% 2.56/1.43  tff(c_180, plain, (![A_100, B_101]: (r2_hidden(A_100, k2_tarski(A_100, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_142])).
% 2.56/1.43  tff(c_183, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_180])).
% 2.56/1.43  tff(c_198, plain, (![D_117, C_118, B_119, A_120]: (r2_hidden(k1_funct_1(D_117, C_118), B_119) | k1_xboole_0=B_119 | ~r2_hidden(C_118, A_120) | ~m1_subset_1(D_117, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(D_117, A_120, B_119) | ~v1_funct_1(D_117))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.43  tff(c_389, plain, (![D_188, A_189, B_190]: (r2_hidden(k1_funct_1(D_188, A_189), B_190) | k1_xboole_0=B_190 | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_189), B_190))) | ~v1_funct_2(D_188, k1_tarski(A_189), B_190) | ~v1_funct_1(D_188))), inference(resolution, [status(thm)], [c_183, c_198])).
% 2.56/1.43  tff(c_392, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_389])).
% 2.56/1.43  tff(c_395, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_392])).
% 2.56/1.43  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_395])).
% 2.56/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.43  
% 2.56/1.43  Inference rules
% 2.56/1.43  ----------------------
% 2.56/1.43  #Ref     : 0
% 2.56/1.43  #Sup     : 78
% 2.56/1.43  #Fact    : 0
% 2.56/1.43  #Define  : 0
% 2.56/1.43  #Split   : 0
% 2.56/1.43  #Chain   : 0
% 2.56/1.43  #Close   : 0
% 2.56/1.43  
% 2.56/1.43  Ordering : KBO
% 2.56/1.43  
% 2.56/1.43  Simplification rules
% 2.56/1.43  ----------------------
% 2.56/1.43  #Subsume      : 0
% 2.56/1.43  #Demod        : 7
% 2.56/1.43  #Tautology    : 36
% 2.56/1.43  #SimpNegUnit  : 1
% 2.56/1.43  #BackRed      : 0
% 2.56/1.43  
% 2.56/1.43  #Partial instantiations: 0
% 2.56/1.43  #Strategies tried      : 1
% 2.56/1.43  
% 2.56/1.43  Timing (in seconds)
% 2.56/1.43  ----------------------
% 2.56/1.43  Preprocessing        : 0.34
% 2.56/1.43  Parsing              : 0.18
% 2.56/1.43  CNF conversion       : 0.02
% 2.56/1.43  Main loop            : 0.27
% 2.56/1.43  Inferencing          : 0.10
% 2.56/1.43  Reduction            : 0.08
% 2.56/1.43  Demodulation         : 0.06
% 2.56/1.43  BG Simplification    : 0.02
% 2.56/1.43  Subsumption          : 0.07
% 2.56/1.43  Abstraction          : 0.02
% 2.56/1.43  MUC search           : 0.00
% 2.56/1.43  Cooper               : 0.00
% 2.56/1.43  Total                : 0.63
% 2.56/1.43  Index Insertion      : 0.00
% 2.56/1.43  Index Deletion       : 0.00
% 2.56/1.43  Index Matching       : 0.00
% 2.56/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
