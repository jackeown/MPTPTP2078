%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 158 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_42,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_14] : ~ r2_hidden(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_205,plain,(
    ! [D_74,C_75,B_76,A_77] :
      ( r2_hidden(k1_funct_1(D_74,C_75),B_76)
      | k1_xboole_0 = B_76
      | ~ r2_hidden(C_75,A_77)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76)))
      | ~ v1_funct_2(D_74,A_77,B_76)
      | ~ v1_funct_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_230,plain,(
    ! [D_78,B_79] :
      ( r2_hidden(k1_funct_1(D_78,'#skF_5'),B_79)
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_79)))
      | ~ v1_funct_2(D_78,'#skF_3',B_79)
      | ~ v1_funct_1(D_78) ) ),
    inference(resolution,[status(thm)],[c_44,c_205])).

tff(c_233,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_230])).

tff(c_240,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_233])).

tff(c_243,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,(
    ! [B_41,A_42] : r2_hidden(B_41,k2_tarski(A_42,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_4])).

tff(c_125,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_122])).

tff(c_253,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_125])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_253])).

tff(c_258,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [E_49,C_50,B_51,A_52] :
      ( E_49 = C_50
      | E_49 = B_51
      | E_49 = A_52
      | ~ r2_hidden(E_49,k1_enumset1(A_52,B_51,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,(
    ! [E_53,B_54,A_55] :
      ( E_53 = B_54
      | E_53 = A_55
      | E_53 = A_55
      | ~ r2_hidden(E_53,k2_tarski(A_55,B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_170,plain,(
    ! [E_53,A_8] :
      ( E_53 = A_8
      | E_53 = A_8
      | E_53 = A_8
      | ~ r2_hidden(E_53,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_264,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_258,c_170])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_42,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.38  
% 2.17/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.38  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.17/1.38  
% 2.17/1.38  %Foreground sorts:
% 2.17/1.38  
% 2.17/1.38  
% 2.17/1.38  %Background operators:
% 2.17/1.38  
% 2.17/1.38  
% 2.17/1.38  %Foreground operators:
% 2.17/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.17/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.17/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.38  
% 2.17/1.40  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.17/1.40  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.40  tff(f_55, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.17/1.40  tff(f_67, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.17/1.40  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.40  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.40  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.17/1.40  tff(c_42, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.40  tff(c_34, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.40  tff(c_82, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.17/1.40  tff(c_85, plain, (![A_14]: (~r2_hidden(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_82])).
% 2.17/1.40  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.40  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.40  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.40  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.40  tff(c_205, plain, (![D_74, C_75, B_76, A_77]: (r2_hidden(k1_funct_1(D_74, C_75), B_76) | k1_xboole_0=B_76 | ~r2_hidden(C_75, A_77) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))) | ~v1_funct_2(D_74, A_77, B_76) | ~v1_funct_1(D_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.40  tff(c_230, plain, (![D_78, B_79]: (r2_hidden(k1_funct_1(D_78, '#skF_5'), B_79) | k1_xboole_0=B_79 | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_79))) | ~v1_funct_2(D_78, '#skF_3', B_79) | ~v1_funct_1(D_78))), inference(resolution, [status(thm)], [c_44, c_205])).
% 2.17/1.40  tff(c_233, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_230])).
% 2.17/1.40  tff(c_240, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_233])).
% 2.17/1.40  tff(c_243, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_240])).
% 2.17/1.40  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.40  tff(c_93, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.40  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.40  tff(c_122, plain, (![B_41, A_42]: (r2_hidden(B_41, k2_tarski(A_42, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_4])).
% 2.17/1.40  tff(c_125, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_122])).
% 2.17/1.40  tff(c_253, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_243, c_125])).
% 2.17/1.40  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_253])).
% 2.17/1.40  tff(c_258, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_240])).
% 2.17/1.40  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.40  tff(c_142, plain, (![E_49, C_50, B_51, A_52]: (E_49=C_50 | E_49=B_51 | E_49=A_52 | ~r2_hidden(E_49, k1_enumset1(A_52, B_51, C_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.40  tff(c_161, plain, (![E_53, B_54, A_55]: (E_53=B_54 | E_53=A_55 | E_53=A_55 | ~r2_hidden(E_53, k2_tarski(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 2.17/1.40  tff(c_170, plain, (![E_53, A_8]: (E_53=A_8 | E_53=A_8 | E_53=A_8 | ~r2_hidden(E_53, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 2.17/1.40  tff(c_264, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_258, c_170])).
% 2.17/1.40  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_42, c_264])).
% 2.17/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.40  
% 2.17/1.40  Inference rules
% 2.17/1.40  ----------------------
% 2.17/1.40  #Ref     : 0
% 2.17/1.40  #Sup     : 49
% 2.17/1.40  #Fact    : 0
% 2.17/1.40  #Define  : 0
% 2.43/1.40  #Split   : 1
% 2.43/1.40  #Chain   : 0
% 2.43/1.40  #Close   : 0
% 2.43/1.40  
% 2.43/1.40  Ordering : KBO
% 2.43/1.40  
% 2.43/1.40  Simplification rules
% 2.43/1.40  ----------------------
% 2.43/1.40  #Subsume      : 3
% 2.43/1.40  #Demod        : 7
% 2.43/1.40  #Tautology    : 24
% 2.43/1.40  #SimpNegUnit  : 3
% 2.43/1.40  #BackRed      : 2
% 2.43/1.40  
% 2.43/1.40  #Partial instantiations: 0
% 2.43/1.40  #Strategies tried      : 1
% 2.43/1.40  
% 2.43/1.40  Timing (in seconds)
% 2.43/1.40  ----------------------
% 2.43/1.40  Preprocessing        : 0.35
% 2.43/1.40  Parsing              : 0.18
% 2.43/1.40  CNF conversion       : 0.02
% 2.43/1.40  Main loop            : 0.23
% 2.43/1.40  Inferencing          : 0.08
% 2.43/1.40  Reduction            : 0.07
% 2.43/1.40  Demodulation         : 0.05
% 2.43/1.40  BG Simplification    : 0.02
% 2.43/1.40  Subsumption          : 0.05
% 2.43/1.40  Abstraction          : 0.02
% 2.43/1.40  MUC search           : 0.00
% 2.43/1.40  Cooper               : 0.00
% 2.43/1.40  Total                : 0.61
% 2.43/1.40  Index Insertion      : 0.00
% 2.43/1.40  Index Deletion       : 0.00
% 2.43/1.40  Index Matching       : 0.00
% 2.43/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
