%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   66 (  76 expanded)
%              Number of leaves         :   39 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 107 expanded)
%              Number of equality atoms :   41 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_41] : k1_setfam_1(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [A_66,B_67] : k1_setfam_1(k2_tarski(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = k1_setfam_1(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_115])).

tff(c_127,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_124])).

tff(c_143,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_143])).

tff(c_155,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_44,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_44])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_290,plain,(
    ! [D_127,C_128,B_129,A_130] :
      ( r2_hidden(k1_funct_1(D_127,C_128),B_129)
      | k1_xboole_0 = B_129
      | ~ r2_hidden(C_128,A_130)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(D_127,A_130,B_129)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_315,plain,(
    ! [D_131,B_132] :
      ( r2_hidden(k1_funct_1(D_131,'#skF_5'),B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(D_131,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_132)))
      | ~ v1_funct_2(D_131,'#skF_3',B_132)
      | ~ v1_funct_1(D_131) ) ),
    inference(resolution,[status(thm)],[c_56,c_290])).

tff(c_318,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_315])).

tff(c_321,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_318])).

tff(c_322,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_321])).

tff(c_32,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,(
    ! [E_84,C_85,B_86,A_87] :
      ( E_84 = C_85
      | E_84 = B_86
      | E_84 = A_87
      | ~ r2_hidden(E_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,(
    ! [E_88,B_89,A_90] :
      ( E_88 = B_89
      | E_88 = A_90
      | E_88 = A_90
      | ~ r2_hidden(E_88,k2_tarski(A_90,B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_233,plain,(
    ! [E_88,A_11] :
      ( E_88 = A_11
      | E_88 = A_11
      | E_88 = A_11
      | ~ r2_hidden(E_88,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_224])).

tff(c_327,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_322,c_233])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.36  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.50/1.36  
% 2.50/1.36  %Foreground sorts:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Background operators:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Foreground operators:
% 2.50/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.50/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.50/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.50/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.50/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.36  
% 2.59/1.38  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.59/1.38  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.59/1.38  tff(f_65, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.59/1.38  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.38  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.59/1.38  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.59/1.38  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.59/1.38  tff(f_79, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.59/1.38  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.59/1.38  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.59/1.38  tff(c_54, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.38  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.38  tff(c_48, plain, (![A_41]: (k1_setfam_1(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.59/1.38  tff(c_30, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.38  tff(c_115, plain, (![A_66, B_67]: (k1_setfam_1(k2_tarski(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.38  tff(c_124, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=k1_setfam_1(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_115])).
% 2.59/1.38  tff(c_127, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_124])).
% 2.59/1.38  tff(c_143, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.38  tff(c_152, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_127, c_143])).
% 2.59/1.38  tff(c_155, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_152])).
% 2.59/1.38  tff(c_44, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.38  tff(c_156, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_44])).
% 2.59/1.38  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.38  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.38  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.38  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.59/1.38  tff(c_290, plain, (![D_127, C_128, B_129, A_130]: (r2_hidden(k1_funct_1(D_127, C_128), B_129) | k1_xboole_0=B_129 | ~r2_hidden(C_128, A_130) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(D_127, A_130, B_129) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.38  tff(c_315, plain, (![D_131, B_132]: (r2_hidden(k1_funct_1(D_131, '#skF_5'), B_132) | k1_xboole_0=B_132 | ~m1_subset_1(D_131, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_132))) | ~v1_funct_2(D_131, '#skF_3', B_132) | ~v1_funct_1(D_131))), inference(resolution, [status(thm)], [c_56, c_290])).
% 2.59/1.38  tff(c_318, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_315])).
% 2.59/1.38  tff(c_321, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_318])).
% 2.59/1.38  tff(c_322, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_156, c_321])).
% 2.59/1.38  tff(c_32, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.38  tff(c_205, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.38  tff(c_224, plain, (![E_88, B_89, A_90]: (E_88=B_89 | E_88=A_90 | E_88=A_90 | ~r2_hidden(E_88, k2_tarski(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_205])).
% 2.59/1.38  tff(c_233, plain, (![E_88, A_11]: (E_88=A_11 | E_88=A_11 | E_88=A_11 | ~r2_hidden(E_88, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_224])).
% 2.59/1.38  tff(c_327, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_322, c_233])).
% 2.59/1.38  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_327])).
% 2.59/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.38  
% 2.59/1.38  Inference rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Ref     : 0
% 2.59/1.38  #Sup     : 59
% 2.59/1.38  #Fact    : 0
% 2.59/1.38  #Define  : 0
% 2.59/1.38  #Split   : 0
% 2.59/1.38  #Chain   : 0
% 2.59/1.38  #Close   : 0
% 2.59/1.38  
% 2.59/1.38  Ordering : KBO
% 2.59/1.38  
% 2.59/1.38  Simplification rules
% 2.59/1.38  ----------------------
% 2.59/1.38  #Subsume      : 0
% 2.59/1.38  #Demod        : 7
% 2.59/1.38  #Tautology    : 38
% 2.59/1.38  #SimpNegUnit  : 4
% 2.59/1.38  #BackRed      : 1
% 2.59/1.38  
% 2.59/1.38  #Partial instantiations: 0
% 2.59/1.38  #Strategies tried      : 1
% 2.59/1.38  
% 2.59/1.38  Timing (in seconds)
% 2.59/1.38  ----------------------
% 2.59/1.38  Preprocessing        : 0.34
% 2.59/1.38  Parsing              : 0.18
% 2.59/1.38  CNF conversion       : 0.02
% 2.59/1.38  Main loop            : 0.22
% 2.59/1.38  Inferencing          : 0.08
% 2.59/1.38  Reduction            : 0.07
% 2.59/1.38  Demodulation         : 0.05
% 2.59/1.38  BG Simplification    : 0.02
% 2.59/1.38  Subsumption          : 0.04
% 2.59/1.38  Abstraction          : 0.02
% 2.59/1.38  MUC search           : 0.00
% 2.59/1.38  Cooper               : 0.00
% 2.59/1.38  Total                : 0.59
% 2.59/1.38  Index Insertion      : 0.00
% 2.59/1.38  Index Deletion       : 0.00
% 2.59/1.38  Index Matching       : 0.00
% 2.59/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
