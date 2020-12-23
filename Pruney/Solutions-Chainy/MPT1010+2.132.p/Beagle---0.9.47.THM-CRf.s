%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  97 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_46,axiom,(
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

tff(c_40,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,(
    ! [A_47,B_48] : k2_tarski(A_47,B_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_36])).

tff(c_104,plain,(
    ! [A_10] : k1_tarski(A_10) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_102])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_182,plain,(
    ! [D_82,C_83,B_84,A_85] :
      ( r2_hidden(k1_funct_1(D_82,C_83),B_84)
      | k1_xboole_0 = B_84
      | ~ r2_hidden(C_83,A_85)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84)))
      | ~ v1_funct_2(D_82,A_85,B_84)
      | ~ v1_funct_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_207,plain,(
    ! [D_86,B_87] :
      ( r2_hidden(k1_funct_1(D_86,'#skF_5'),B_87)
      | k1_xboole_0 = B_87
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_87)))
      | ~ v1_funct_2(D_86,'#skF_3',B_87)
      | ~ v1_funct_1(D_86) ) ),
    inference(resolution,[status(thm)],[c_42,c_182])).

tff(c_210,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_207])).

tff(c_213,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_210])).

tff(c_214,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_213])).

tff(c_30,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [E_57,C_58,B_59,A_60] :
      ( E_57 = C_58
      | E_57 = B_59
      | E_57 = A_60
      | ~ r2_hidden(E_57,k1_enumset1(A_60,B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [E_61,B_62,A_63] :
      ( E_61 = B_62
      | E_61 = A_63
      | E_61 = A_63
      | ~ r2_hidden(E_61,k2_tarski(A_63,B_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_124])).

tff(c_152,plain,(
    ! [E_61,A_10] :
      ( E_61 = A_10
      | E_61 = A_10
      | E_61 = A_10
      | ~ r2_hidden(E_61,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_143])).

tff(c_219,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_214,c_152])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.19/1.24  
% 2.19/1.24  %Foreground sorts:
% 2.19/1.24  
% 2.19/1.24  
% 2.19/1.24  %Background operators:
% 2.19/1.24  
% 2.19/1.24  
% 2.19/1.24  %Foreground operators:
% 2.19/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.19/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.19/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.24  
% 2.19/1.25  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.19/1.25  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.25  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.19/1.25  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.19/1.25  tff(f_65, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.19/1.25  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/1.25  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.19/1.25  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.25  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.25  tff(c_91, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.25  tff(c_36, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.25  tff(c_102, plain, (![A_47, B_48]: (k2_tarski(A_47, B_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91, c_36])).
% 2.19/1.25  tff(c_104, plain, (![A_10]: (k1_tarski(A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_102])).
% 2.19/1.25  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.25  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.25  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.25  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.25  tff(c_182, plain, (![D_82, C_83, B_84, A_85]: (r2_hidden(k1_funct_1(D_82, C_83), B_84) | k1_xboole_0=B_84 | ~r2_hidden(C_83, A_85) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))) | ~v1_funct_2(D_82, A_85, B_84) | ~v1_funct_1(D_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.25  tff(c_207, plain, (![D_86, B_87]: (r2_hidden(k1_funct_1(D_86, '#skF_5'), B_87) | k1_xboole_0=B_87 | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_87))) | ~v1_funct_2(D_86, '#skF_3', B_87) | ~v1_funct_1(D_86))), inference(resolution, [status(thm)], [c_42, c_182])).
% 2.19/1.25  tff(c_210, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_207])).
% 2.19/1.25  tff(c_213, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_210])).
% 2.19/1.25  tff(c_214, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_104, c_213])).
% 2.19/1.25  tff(c_30, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.25  tff(c_124, plain, (![E_57, C_58, B_59, A_60]: (E_57=C_58 | E_57=B_59 | E_57=A_60 | ~r2_hidden(E_57, k1_enumset1(A_60, B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.25  tff(c_143, plain, (![E_61, B_62, A_63]: (E_61=B_62 | E_61=A_63 | E_61=A_63 | ~r2_hidden(E_61, k2_tarski(A_63, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_124])).
% 2.19/1.25  tff(c_152, plain, (![E_61, A_10]: (E_61=A_10 | E_61=A_10 | E_61=A_10 | ~r2_hidden(E_61, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_143])).
% 2.19/1.25  tff(c_219, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_214, c_152])).
% 2.19/1.25  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_219])).
% 2.19/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  Inference rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Ref     : 0
% 2.19/1.25  #Sup     : 39
% 2.19/1.25  #Fact    : 0
% 2.19/1.25  #Define  : 0
% 2.19/1.25  #Split   : 0
% 2.19/1.25  #Chain   : 0
% 2.19/1.25  #Close   : 0
% 2.19/1.25  
% 2.19/1.25  Ordering : KBO
% 2.19/1.25  
% 2.19/1.25  Simplification rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Subsume      : 0
% 2.19/1.25  #Demod        : 4
% 2.19/1.25  #Tautology    : 18
% 2.19/1.25  #SimpNegUnit  : 2
% 2.19/1.25  #BackRed      : 0
% 2.19/1.25  
% 2.19/1.25  #Partial instantiations: 0
% 2.19/1.25  #Strategies tried      : 1
% 2.19/1.25  
% 2.19/1.25  Timing (in seconds)
% 2.19/1.25  ----------------------
% 2.19/1.26  Preprocessing        : 0.31
% 2.19/1.26  Parsing              : 0.16
% 2.19/1.26  CNF conversion       : 0.02
% 2.19/1.26  Main loop            : 0.20
% 2.19/1.26  Inferencing          : 0.07
% 2.19/1.26  Reduction            : 0.06
% 2.19/1.26  Demodulation         : 0.04
% 2.19/1.26  BG Simplification    : 0.01
% 2.19/1.26  Subsumption          : 0.04
% 2.19/1.26  Abstraction          : 0.02
% 2.19/1.26  MUC search           : 0.00
% 2.19/1.26  Cooper               : 0.00
% 2.19/1.26  Total                : 0.53
% 2.19/1.26  Index Insertion      : 0.00
% 2.19/1.26  Index Deletion       : 0.00
% 2.19/1.26  Index Matching       : 0.00
% 2.19/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
