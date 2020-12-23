%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 130 expanded)
%              Number of equality atoms :   52 (  64 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_52,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_188,plain,(
    ! [D_93,C_94,B_95,A_96] :
      ( r2_hidden(k1_funct_1(D_93,C_94),B_95)
      | k1_xboole_0 = B_95
      | ~ r2_hidden(C_94,A_96)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_2(D_93,A_96,B_95)
      | ~ v1_funct_1(D_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_243,plain,(
    ! [D_104,B_105] :
      ( r2_hidden(k1_funct_1(D_104,'#skF_5'),B_105)
      | k1_xboole_0 = B_105
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_105)))
      | ~ v1_funct_2(D_104,'#skF_3',B_105)
      | ~ v1_funct_1(D_104) ) ),
    inference(resolution,[status(thm)],[c_54,c_188])).

tff(c_246,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_249,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_246])).

tff(c_250,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_249])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [D_74,B_77,G_75,E_73,A_78,C_76] :
      ( G_75 = E_73
      | G_75 = D_74
      | G_75 = C_76
      | G_75 = B_77
      | G_75 = A_78
      | ~ r2_hidden(G_75,k3_enumset1(A_78,B_77,C_76,D_74,E_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_262,plain,(
    ! [C_110,A_108,D_112,B_109,G_111] :
      ( G_111 = D_112
      | G_111 = C_110
      | G_111 = B_109
      | G_111 = A_108
      | G_111 = A_108
      | ~ r2_hidden(G_111,k2_enumset1(A_108,B_109,C_110,D_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_286,plain,(
    ! [G_113,C_114,B_115,A_116] :
      ( G_113 = C_114
      | G_113 = B_115
      | G_113 = A_116
      | G_113 = A_116
      | G_113 = A_116
      | ~ r2_hidden(G_113,k1_enumset1(A_116,B_115,C_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_262])).

tff(c_305,plain,(
    ! [G_117,B_118,A_119] :
      ( G_117 = B_118
      | G_117 = A_119
      | G_117 = A_119
      | G_117 = A_119
      | G_117 = A_119
      | ~ r2_hidden(G_117,k2_tarski(A_119,B_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_286])).

tff(c_320,plain,(
    ! [G_126,A_127] :
      ( G_126 = A_127
      | G_126 = A_127
      | G_126 = A_127
      | G_126 = A_127
      | G_126 = A_127
      | ~ r2_hidden(G_126,k1_tarski(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_305])).

tff(c_323,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_250,c_320])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_52,c_52,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:48:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.37  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.47/1.37  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.47/1.37  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.47/1.37  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.47/1.37  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.37  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.47/1.37  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.47/1.37  tff(f_59, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.47/1.37  tff(c_52, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.37  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.37  tff(c_70, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.37  tff(c_74, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 2.47/1.37  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.37  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.37  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.37  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.37  tff(c_188, plain, (![D_93, C_94, B_95, A_96]: (r2_hidden(k1_funct_1(D_93, C_94), B_95) | k1_xboole_0=B_95 | ~r2_hidden(C_94, A_96) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_2(D_93, A_96, B_95) | ~v1_funct_1(D_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.47/1.37  tff(c_243, plain, (![D_104, B_105]: (r2_hidden(k1_funct_1(D_104, '#skF_5'), B_105) | k1_xboole_0=B_105 | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_105))) | ~v1_funct_2(D_104, '#skF_3', B_105) | ~v1_funct_1(D_104))), inference(resolution, [status(thm)], [c_54, c_188])).
% 2.47/1.37  tff(c_246, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_243])).
% 2.47/1.37  tff(c_249, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_246])).
% 2.47/1.37  tff(c_250, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_249])).
% 2.47/1.37  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.37  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.37  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.37  tff(c_140, plain, (![D_74, B_77, G_75, E_73, A_78, C_76]: (G_75=E_73 | G_75=D_74 | G_75=C_76 | G_75=B_77 | G_75=A_78 | ~r2_hidden(G_75, k3_enumset1(A_78, B_77, C_76, D_74, E_73)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.37  tff(c_262, plain, (![C_110, A_108, D_112, B_109, G_111]: (G_111=D_112 | G_111=C_110 | G_111=B_109 | G_111=A_108 | G_111=A_108 | ~r2_hidden(G_111, k2_enumset1(A_108, B_109, C_110, D_112)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 2.47/1.37  tff(c_286, plain, (![G_113, C_114, B_115, A_116]: (G_113=C_114 | G_113=B_115 | G_113=A_116 | G_113=A_116 | G_113=A_116 | ~r2_hidden(G_113, k1_enumset1(A_116, B_115, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_262])).
% 2.47/1.37  tff(c_305, plain, (![G_117, B_118, A_119]: (G_117=B_118 | G_117=A_119 | G_117=A_119 | G_117=A_119 | G_117=A_119 | ~r2_hidden(G_117, k2_tarski(A_119, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_286])).
% 2.47/1.37  tff(c_320, plain, (![G_126, A_127]: (G_126=A_127 | G_126=A_127 | G_126=A_127 | G_126=A_127 | G_126=A_127 | ~r2_hidden(G_126, k1_tarski(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_305])).
% 2.47/1.37  tff(c_323, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_250, c_320])).
% 2.47/1.37  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_52, c_52, c_323])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 63
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 0
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 0
% 2.47/1.37  #Demod        : 6
% 2.47/1.37  #Tautology    : 28
% 2.47/1.37  #SimpNegUnit  : 2
% 2.47/1.37  #BackRed      : 0
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.34
% 2.47/1.37  Parsing              : 0.17
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.24
% 2.47/1.37  Inferencing          : 0.08
% 2.47/1.37  Reduction            : 0.07
% 2.47/1.37  Demodulation         : 0.05
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.06
% 2.47/1.37  Abstraction          : 0.02
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.61
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
