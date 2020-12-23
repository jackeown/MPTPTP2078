%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 158 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_200,plain,(
    ! [D_81,C_82,B_83,A_84] :
      ( r2_hidden(k1_funct_1(D_81,C_82),B_83)
      | k1_xboole_0 = B_83
      | ~ r2_hidden(C_82,A_84)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(D_81,A_84,B_83)
      | ~ v1_funct_1(D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_226,plain,(
    ! [D_89,B_90] :
      ( r2_hidden(k1_funct_1(D_89,'#skF_5'),B_90)
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_90)))
      | ~ v1_funct_2(D_89,'#skF_3',B_90)
      | ~ v1_funct_1(D_89) ) ),
    inference(resolution,[status(thm)],[c_38,c_200])).

tff(c_229,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_226])).

tff(c_232,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_229])).

tff(c_233,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_42,B_43] : r2_hidden(A_42,k2_tarski(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_113,plain,(
    ! [A_44] : r2_hidden(A_44,k1_tarski(A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_105])).

tff(c_32,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [A_44] : ~ r1_tarski(k1_tarski(A_44),A_44) ),
    inference(resolution,[status(thm)],[c_113,c_32])).

tff(c_242,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_117])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_251,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [E_46,C_47,B_48,A_49] :
      ( E_46 = C_47
      | E_46 = B_48
      | E_46 = A_49
      | ~ r2_hidden(E_46,k1_enumset1(A_49,B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,(
    ! [E_60,B_61,A_62] :
      ( E_60 = B_61
      | E_60 = A_62
      | E_60 = A_62
      | ~ r2_hidden(E_60,k2_tarski(A_62,B_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_166,plain,(
    ! [E_60,A_9] :
      ( E_60 = A_9
      | E_60 = A_9
      | E_60 = A_9
      | ~ r2_hidden(E_60,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_257,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_251,c_166])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_36,c_257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.30  
% 2.04/1.30  %Foreground sorts:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Background operators:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Foreground operators:
% 2.04/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.04/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.04/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.30  
% 2.34/1.31  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.34/1.31  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.31  tff(f_63, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.34/1.31  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.31  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.31  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.34/1.31  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.34/1.31  tff(c_36, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.31  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.31  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.31  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.31  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.31  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.34/1.31  tff(c_200, plain, (![D_81, C_82, B_83, A_84]: (r2_hidden(k1_funct_1(D_81, C_82), B_83) | k1_xboole_0=B_83 | ~r2_hidden(C_82, A_84) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(D_81, A_84, B_83) | ~v1_funct_1(D_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.34/1.31  tff(c_226, plain, (![D_89, B_90]: (r2_hidden(k1_funct_1(D_89, '#skF_5'), B_90) | k1_xboole_0=B_90 | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_90))) | ~v1_funct_2(D_89, '#skF_3', B_90) | ~v1_funct_1(D_89))), inference(resolution, [status(thm)], [c_38, c_200])).
% 2.34/1.31  tff(c_229, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_226])).
% 2.34/1.31  tff(c_232, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_229])).
% 2.34/1.31  tff(c_233, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_232])).
% 2.34/1.31  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.31  tff(c_78, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.31  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.31  tff(c_105, plain, (![A_42, B_43]: (r2_hidden(A_42, k2_tarski(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 2.34/1.31  tff(c_113, plain, (![A_44]: (r2_hidden(A_44, k1_tarski(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_105])).
% 2.34/1.31  tff(c_32, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.31  tff(c_117, plain, (![A_44]: (~r1_tarski(k1_tarski(A_44), A_44))), inference(resolution, [status(thm)], [c_113, c_32])).
% 2.34/1.31  tff(c_242, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_233, c_117])).
% 2.34/1.31  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_242])).
% 2.34/1.31  tff(c_251, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_232])).
% 2.34/1.31  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.31  tff(c_119, plain, (![E_46, C_47, B_48, A_49]: (E_46=C_47 | E_46=B_48 | E_46=A_49 | ~r2_hidden(E_46, k1_enumset1(A_49, B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.31  tff(c_157, plain, (![E_60, B_61, A_62]: (E_60=B_61 | E_60=A_62 | E_60=A_62 | ~r2_hidden(E_60, k2_tarski(A_62, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_119])).
% 2.34/1.31  tff(c_166, plain, (![E_60, A_9]: (E_60=A_9 | E_60=A_9 | E_60=A_9 | ~r2_hidden(E_60, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_157])).
% 2.34/1.31  tff(c_257, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_251, c_166])).
% 2.34/1.31  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_36, c_257])).
% 2.34/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  Inference rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Ref     : 0
% 2.34/1.31  #Sup     : 50
% 2.34/1.31  #Fact    : 0
% 2.34/1.31  #Define  : 0
% 2.34/1.31  #Split   : 1
% 2.34/1.31  #Chain   : 0
% 2.34/1.31  #Close   : 0
% 2.34/1.31  
% 2.34/1.31  Ordering : KBO
% 2.34/1.31  
% 2.34/1.31  Simplification rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Subsume      : 5
% 2.34/1.31  #Demod        : 7
% 2.34/1.31  #Tautology    : 13
% 2.34/1.31  #SimpNegUnit  : 1
% 2.34/1.31  #BackRed      : 2
% 2.34/1.31  
% 2.34/1.31  #Partial instantiations: 0
% 2.34/1.31  #Strategies tried      : 1
% 2.34/1.31  
% 2.34/1.31  Timing (in seconds)
% 2.34/1.31  ----------------------
% 2.34/1.32  Preprocessing        : 0.32
% 2.34/1.32  Parsing              : 0.17
% 2.34/1.32  CNF conversion       : 0.02
% 2.34/1.32  Main loop            : 0.22
% 2.34/1.32  Inferencing          : 0.08
% 2.34/1.32  Reduction            : 0.06
% 2.34/1.32  Demodulation         : 0.05
% 2.34/1.32  BG Simplification    : 0.01
% 2.34/1.32  Subsumption          : 0.05
% 2.34/1.32  Abstraction          : 0.02
% 2.34/1.32  MUC search           : 0.00
% 2.34/1.32  Cooper               : 0.00
% 2.34/1.32  Total                : 0.57
% 2.34/1.32  Index Insertion      : 0.00
% 2.34/1.32  Index Deletion       : 0.00
% 2.34/1.32  Index Matching       : 0.00
% 2.34/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
