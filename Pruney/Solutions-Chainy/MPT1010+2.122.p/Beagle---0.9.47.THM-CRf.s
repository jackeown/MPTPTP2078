%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 137 expanded)
%              Number of equality atoms :   54 (  66 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_58,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [B_36] : k2_xboole_0(B_36,B_36) = B_36 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),B_16) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [A_15] : k1_tarski(A_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_209,plain,(
    ! [D_101,C_102,B_103,A_104] :
      ( r2_hidden(k1_funct_1(D_101,C_102),B_103)
      | k1_xboole_0 = B_103
      | ~ r2_hidden(C_102,A_104)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(D_101,A_104,B_103)
      | ~ v1_funct_1(D_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_335,plain,(
    ! [D_134,B_135] :
      ( r2_hidden(k1_funct_1(D_134,'#skF_5'),B_135)
      | k1_xboole_0 = B_135
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_135)))
      | ~ v1_funct_2(D_134,'#skF_3',B_135)
      | ~ v1_funct_1(D_134) ) ),
    inference(resolution,[status(thm)],[c_60,c_209])).

tff(c_338,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_335])).

tff(c_341,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_338])).

tff(c_342,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_341])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [G_92,D_91,A_89,B_90,C_88,E_93] :
      ( G_92 = E_93
      | G_92 = D_91
      | G_92 = C_88
      | G_92 = B_90
      | G_92 = A_89
      | ~ r2_hidden(G_92,k3_enumset1(A_89,B_90,C_88,D_91,E_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_271,plain,(
    ! [C_114,A_116,D_118,G_115,B_117] :
      ( G_115 = D_118
      | G_115 = C_114
      | G_115 = B_117
      | G_115 = A_116
      | G_115 = A_116
      | ~ r2_hidden(G_115,k2_enumset1(A_116,B_117,C_114,D_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_169])).

tff(c_295,plain,(
    ! [G_119,C_120,B_121,A_122] :
      ( G_119 = C_120
      | G_119 = B_121
      | G_119 = A_122
      | G_119 = A_122
      | G_119 = A_122
      | ~ r2_hidden(G_119,k1_enumset1(A_122,B_121,C_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_271])).

tff(c_315,plain,(
    ! [G_129,B_130,A_131] :
      ( G_129 = B_130
      | G_129 = A_131
      | G_129 = A_131
      | G_129 = A_131
      | G_129 = A_131
      | ~ r2_hidden(G_129,k2_tarski(A_131,B_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_295])).

tff(c_324,plain,(
    ! [G_129,A_5] :
      ( G_129 = A_5
      | G_129 = A_5
      | G_129 = A_5
      | G_129 = A_5
      | G_129 = A_5
      | ~ r2_hidden(G_129,k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_315])).

tff(c_345,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_342,c_324])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_58,c_58,c_58,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.25  
% 2.34/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.25  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.34/1.25  
% 2.34/1.25  %Foreground sorts:
% 2.34/1.25  
% 2.34/1.25  
% 2.34/1.25  %Background operators:
% 2.34/1.25  
% 2.34/1.25  
% 2.34/1.25  %Foreground operators:
% 2.34/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.25  
% 2.34/1.26  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.34/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.34/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.34/1.26  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.34/1.26  tff(f_79, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.34/1.26  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.26  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.26  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.34/1.26  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.34/1.26  tff(f_67, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.34/1.26  tff(c_58, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.26  tff(c_79, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.26  tff(c_84, plain, (![B_36]: (k2_xboole_0(B_36, B_36)=B_36)), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.34/1.26  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.26  tff(c_91, plain, (![A_15]: (k1_tarski(A_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 2.34/1.26  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.26  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.26  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.26  tff(c_60, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.26  tff(c_209, plain, (![D_101, C_102, B_103, A_104]: (r2_hidden(k1_funct_1(D_101, C_102), B_103) | k1_xboole_0=B_103 | ~r2_hidden(C_102, A_104) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(D_101, A_104, B_103) | ~v1_funct_1(D_101))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.26  tff(c_335, plain, (![D_134, B_135]: (r2_hidden(k1_funct_1(D_134, '#skF_5'), B_135) | k1_xboole_0=B_135 | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_135))) | ~v1_funct_2(D_134, '#skF_3', B_135) | ~v1_funct_1(D_134))), inference(resolution, [status(thm)], [c_60, c_209])).
% 2.34/1.26  tff(c_338, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_335])).
% 2.34/1.26  tff(c_341, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_338])).
% 2.34/1.26  tff(c_342, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_341])).
% 2.34/1.26  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.26  tff(c_12, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.26  tff(c_14, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.26  tff(c_16, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.26  tff(c_169, plain, (![G_92, D_91, A_89, B_90, C_88, E_93]: (G_92=E_93 | G_92=D_91 | G_92=C_88 | G_92=B_90 | G_92=A_89 | ~r2_hidden(G_92, k3_enumset1(A_89, B_90, C_88, D_91, E_93)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.34/1.26  tff(c_271, plain, (![C_114, A_116, D_118, G_115, B_117]: (G_115=D_118 | G_115=C_114 | G_115=B_117 | G_115=A_116 | G_115=A_116 | ~r2_hidden(G_115, k2_enumset1(A_116, B_117, C_114, D_118)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_169])).
% 2.34/1.26  tff(c_295, plain, (![G_119, C_120, B_121, A_122]: (G_119=C_120 | G_119=B_121 | G_119=A_122 | G_119=A_122 | G_119=A_122 | ~r2_hidden(G_119, k1_enumset1(A_122, B_121, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_271])).
% 2.34/1.26  tff(c_315, plain, (![G_129, B_130, A_131]: (G_129=B_130 | G_129=A_131 | G_129=A_131 | G_129=A_131 | G_129=A_131 | ~r2_hidden(G_129, k2_tarski(A_131, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_295])).
% 2.34/1.26  tff(c_324, plain, (![G_129, A_5]: (G_129=A_5 | G_129=A_5 | G_129=A_5 | G_129=A_5 | G_129=A_5 | ~r2_hidden(G_129, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_315])).
% 2.34/1.26  tff(c_345, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_342, c_324])).
% 2.34/1.26  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_58, c_58, c_58, c_345])).
% 2.34/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.26  
% 2.34/1.26  Inference rules
% 2.34/1.26  ----------------------
% 2.34/1.26  #Ref     : 0
% 2.34/1.26  #Sup     : 65
% 2.34/1.26  #Fact    : 0
% 2.34/1.26  #Define  : 0
% 2.34/1.26  #Split   : 0
% 2.34/1.26  #Chain   : 0
% 2.34/1.26  #Close   : 0
% 2.34/1.26  
% 2.34/1.26  Ordering : KBO
% 2.34/1.26  
% 2.34/1.26  Simplification rules
% 2.34/1.26  ----------------------
% 2.34/1.26  #Subsume      : 0
% 2.34/1.26  #Demod        : 8
% 2.34/1.26  #Tautology    : 31
% 2.34/1.26  #SimpNegUnit  : 2
% 2.34/1.26  #BackRed      : 0
% 2.34/1.26  
% 2.34/1.26  #Partial instantiations: 0
% 2.34/1.26  #Strategies tried      : 1
% 2.34/1.26  
% 2.34/1.26  Timing (in seconds)
% 2.34/1.26  ----------------------
% 2.34/1.27  Preprocessing        : 0.29
% 2.34/1.27  Parsing              : 0.14
% 2.34/1.27  CNF conversion       : 0.02
% 2.34/1.27  Main loop            : 0.24
% 2.34/1.27  Inferencing          : 0.08
% 2.34/1.27  Reduction            : 0.07
% 2.34/1.27  Demodulation         : 0.05
% 2.34/1.27  BG Simplification    : 0.02
% 2.34/1.27  Subsumption          : 0.06
% 2.34/1.27  Abstraction          : 0.02
% 2.34/1.27  MUC search           : 0.00
% 2.34/1.27  Cooper               : 0.00
% 2.34/1.27  Total                : 0.56
% 2.34/1.27  Index Insertion      : 0.00
% 2.34/1.27  Index Deletion       : 0.00
% 2.34/1.27  Index Matching       : 0.00
% 2.34/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
