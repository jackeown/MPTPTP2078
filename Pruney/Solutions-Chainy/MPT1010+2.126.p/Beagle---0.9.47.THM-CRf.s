%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   36 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  98 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_81,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [A_70,B_71] : k4_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [A_10] : k4_xboole_0(k1_tarski(A_10),k1_tarski(A_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_44,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_44])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_334,plain,(
    ! [D_135,C_136,B_137,A_138] :
      ( r2_hidden(k1_funct_1(D_135,C_136),B_137)
      | k1_xboole_0 = B_137
      | ~ r2_hidden(C_136,A_138)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(D_135,A_138,B_137)
      | ~ v1_funct_1(D_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_359,plain,(
    ! [D_139,B_140] :
      ( r2_hidden(k1_funct_1(D_139,'#skF_5'),B_140)
      | k1_xboole_0 = B_140
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_140)))
      | ~ v1_funct_2(D_139,'#skF_3',B_140)
      | ~ v1_funct_1(D_139) ) ),
    inference(resolution,[status(thm)],[c_58,c_334])).

tff(c_362,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_359])).

tff(c_365,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_362])).

tff(c_366,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_365])).

tff(c_30,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_249,plain,(
    ! [E_92,C_93,B_94,A_95] :
      ( E_92 = C_93
      | E_92 = B_94
      | E_92 = A_95
      | ~ r2_hidden(E_92,k1_enumset1(A_95,B_94,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_277,plain,(
    ! [E_101,B_102,A_103] :
      ( E_101 = B_102
      | E_101 = A_103
      | E_101 = A_103
      | ~ r2_hidden(E_101,k2_tarski(A_103,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_249])).

tff(c_286,plain,(
    ! [E_101,A_10] :
      ( E_101 = A_10
      | E_101 = A_10
      | E_101 = A_10
      | ~ r2_hidden(E_101,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_277])).

tff(c_371,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_366,c_286])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:15:35 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.36/1.30  
% 2.36/1.30  %Foreground sorts:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Background operators:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Foreground operators:
% 2.36/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.36/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.36/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.30  
% 2.36/1.32  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.36/1.32  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.32  tff(f_65, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.36/1.32  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.36/1.32  tff(f_81, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.36/1.32  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.32  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.36/1.32  tff(c_56, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.36/1.32  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.32  tff(c_131, plain, (![A_70, B_71]: (k4_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.32  tff(c_138, plain, (![A_10]: (k4_xboole_0(k1_tarski(A_10), k1_tarski(A_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_131])).
% 2.36/1.32  tff(c_44, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.32  tff(c_161, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_44])).
% 2.36/1.32  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.36/1.32  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.36/1.32  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.36/1.32  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.36/1.32  tff(c_334, plain, (![D_135, C_136, B_137, A_138]: (r2_hidden(k1_funct_1(D_135, C_136), B_137) | k1_xboole_0=B_137 | ~r2_hidden(C_136, A_138) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(D_135, A_138, B_137) | ~v1_funct_1(D_135))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.32  tff(c_359, plain, (![D_139, B_140]: (r2_hidden(k1_funct_1(D_139, '#skF_5'), B_140) | k1_xboole_0=B_140 | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_140))) | ~v1_funct_2(D_139, '#skF_3', B_140) | ~v1_funct_1(D_139))), inference(resolution, [status(thm)], [c_58, c_334])).
% 2.36/1.32  tff(c_362, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_359])).
% 2.36/1.32  tff(c_365, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_362])).
% 2.36/1.32  tff(c_366, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_161, c_365])).
% 2.36/1.32  tff(c_30, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.32  tff(c_249, plain, (![E_92, C_93, B_94, A_95]: (E_92=C_93 | E_92=B_94 | E_92=A_95 | ~r2_hidden(E_92, k1_enumset1(A_95, B_94, C_93)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.32  tff(c_277, plain, (![E_101, B_102, A_103]: (E_101=B_102 | E_101=A_103 | E_101=A_103 | ~r2_hidden(E_101, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_249])).
% 2.36/1.32  tff(c_286, plain, (![E_101, A_10]: (E_101=A_10 | E_101=A_10 | E_101=A_10 | ~r2_hidden(E_101, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_277])).
% 2.36/1.32  tff(c_371, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_366, c_286])).
% 2.36/1.32  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_371])).
% 2.36/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  Inference rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Ref     : 0
% 2.36/1.32  #Sup     : 70
% 2.36/1.32  #Fact    : 0
% 2.36/1.32  #Define  : 0
% 2.36/1.32  #Split   : 0
% 2.36/1.32  #Chain   : 0
% 2.36/1.32  #Close   : 0
% 2.36/1.32  
% 2.36/1.32  Ordering : KBO
% 2.36/1.32  
% 2.36/1.32  Simplification rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Subsume      : 0
% 2.36/1.32  #Demod        : 10
% 2.36/1.32  #Tautology    : 47
% 2.36/1.32  #SimpNegUnit  : 4
% 2.36/1.32  #BackRed      : 1
% 2.36/1.32  
% 2.36/1.32  #Partial instantiations: 0
% 2.36/1.32  #Strategies tried      : 1
% 2.36/1.32  
% 2.36/1.32  Timing (in seconds)
% 2.36/1.32  ----------------------
% 2.36/1.32  Preprocessing        : 0.34
% 2.36/1.32  Parsing              : 0.18
% 2.36/1.32  CNF conversion       : 0.02
% 2.36/1.32  Main loop            : 0.23
% 2.36/1.32  Inferencing          : 0.08
% 2.36/1.32  Reduction            : 0.07
% 2.36/1.32  Demodulation         : 0.05
% 2.36/1.32  BG Simplification    : 0.02
% 2.36/1.32  Subsumption          : 0.04
% 2.36/1.32  Abstraction          : 0.02
% 2.36/1.32  MUC search           : 0.00
% 2.36/1.32  Cooper               : 0.00
% 2.36/1.32  Total                : 0.59
% 2.36/1.32  Index Insertion      : 0.00
% 2.36/1.32  Index Deletion       : 0.00
% 2.36/1.32  Index Matching       : 0.00
% 2.36/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
