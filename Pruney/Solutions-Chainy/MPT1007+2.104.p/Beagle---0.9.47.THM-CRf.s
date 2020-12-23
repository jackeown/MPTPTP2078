%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  74 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_54,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_55,B_56,C_57,D_58] : k3_enumset1(A_55,A_55,B_56,C_57,D_58) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [D_14,G_19,E_15,B_12,C_13] : r2_hidden(G_19,k3_enumset1(G_19,B_12,C_13,D_14,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,(
    ! [A_59,B_60,C_61,D_62] : r2_hidden(A_59,k2_enumset1(A_59,B_60,C_61,D_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_20])).

tff(c_146,plain,(
    ! [A_69,B_70,C_71] : r2_hidden(A_69,k1_enumset1(A_69,B_70,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_150,plain,(
    ! [A_72,B_73] : r2_hidden(A_72,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_146])).

tff(c_153,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_155,plain,(
    ! [D_75,C_76,B_77,A_78] :
      ( r2_hidden(k1_funct_1(D_75,C_76),B_77)
      | k1_xboole_0 = B_77
      | ~ r2_hidden(C_76,A_78)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77)))
      | ~ v1_funct_2(D_75,A_78,B_77)
      | ~ v1_funct_1(D_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_294,plain,(
    ! [D_125,A_126,B_127] :
      ( r2_hidden(k1_funct_1(D_125,A_126),B_127)
      | k1_xboole_0 = B_127
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_126),B_127)))
      | ~ v1_funct_2(D_125,k1_tarski(A_126),B_127)
      | ~ v1_funct_1(D_125) ) ),
    inference(resolution,[status(thm)],[c_153,c_155])).

tff(c_297,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_294])).

tff(c_300,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.46/1.35  
% 2.46/1.35  %Foreground sorts:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Background operators:
% 2.46/1.35  
% 2.46/1.35  
% 2.46/1.35  %Foreground operators:
% 2.46/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.35  
% 2.46/1.36  tff(f_78, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.46/1.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.36  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.46/1.36  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.46/1.36  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.46/1.36  tff(f_54, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.46/1.36  tff(f_66, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.46/1.36  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.36  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.36  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.36  tff(c_54, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.36  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.46/1.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.36  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.36  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.36  tff(c_89, plain, (![A_55, B_56, C_57, D_58]: (k3_enumset1(A_55, A_55, B_56, C_57, D_58)=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.36  tff(c_20, plain, (![D_14, G_19, E_15, B_12, C_13]: (r2_hidden(G_19, k3_enumset1(G_19, B_12, C_13, D_14, E_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.46/1.36  tff(c_113, plain, (![A_59, B_60, C_61, D_62]: (r2_hidden(A_59, k2_enumset1(A_59, B_60, C_61, D_62)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_20])).
% 2.46/1.36  tff(c_146, plain, (![A_69, B_70, C_71]: (r2_hidden(A_69, k1_enumset1(A_69, B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_113])).
% 2.46/1.36  tff(c_150, plain, (![A_72, B_73]: (r2_hidden(A_72, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_146])).
% 2.46/1.36  tff(c_153, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 2.46/1.36  tff(c_155, plain, (![D_75, C_76, B_77, A_78]: (r2_hidden(k1_funct_1(D_75, C_76), B_77) | k1_xboole_0=B_77 | ~r2_hidden(C_76, A_78) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))) | ~v1_funct_2(D_75, A_78, B_77) | ~v1_funct_1(D_75))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.36  tff(c_294, plain, (![D_125, A_126, B_127]: (r2_hidden(k1_funct_1(D_125, A_126), B_127) | k1_xboole_0=B_127 | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_126), B_127))) | ~v1_funct_2(D_125, k1_tarski(A_126), B_127) | ~v1_funct_1(D_125))), inference(resolution, [status(thm)], [c_153, c_155])).
% 2.46/1.36  tff(c_297, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_294])).
% 2.46/1.36  tff(c_300, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_297])).
% 2.46/1.36  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_300])).
% 2.46/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  Inference rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Ref     : 0
% 2.46/1.36  #Sup     : 57
% 2.46/1.36  #Fact    : 0
% 2.46/1.36  #Define  : 0
% 2.46/1.36  #Split   : 0
% 2.46/1.36  #Chain   : 0
% 2.46/1.36  #Close   : 0
% 2.46/1.36  
% 2.46/1.36  Ordering : KBO
% 2.46/1.36  
% 2.46/1.36  Simplification rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Subsume      : 0
% 2.46/1.36  #Demod        : 6
% 2.46/1.36  #Tautology    : 27
% 2.46/1.36  #SimpNegUnit  : 1
% 2.46/1.36  #BackRed      : 0
% 2.46/1.36  
% 2.46/1.36  #Partial instantiations: 0
% 2.46/1.36  #Strategies tried      : 1
% 2.46/1.36  
% 2.46/1.36  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.37  Preprocessing        : 0.33
% 2.46/1.37  Parsing              : 0.16
% 2.46/1.37  CNF conversion       : 0.03
% 2.46/1.37  Main loop            : 0.26
% 2.46/1.37  Inferencing          : 0.09
% 2.46/1.37  Reduction            : 0.08
% 2.46/1.37  Demodulation         : 0.06
% 2.46/1.37  BG Simplification    : 0.02
% 2.46/1.37  Subsumption          : 0.06
% 2.46/1.37  Abstraction          : 0.02
% 2.46/1.37  MUC search           : 0.00
% 2.46/1.37  Cooper               : 0.00
% 2.46/1.37  Total                : 0.62
% 2.46/1.37  Index Insertion      : 0.00
% 2.46/1.37  Index Deletion       : 0.00
% 2.46/1.37  Index Matching       : 0.00
% 2.46/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
