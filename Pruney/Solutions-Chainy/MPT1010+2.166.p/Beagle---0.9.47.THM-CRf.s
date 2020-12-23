%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   62 (  66 expanded)
%              Number of leaves         :   38 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  79 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_39] : k1_setfam_1(k1_tarski(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = k1_setfam_1(k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_105,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_115,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_115])).

tff(c_127,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_32,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [B_38] : k1_tarski(B_38) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_32])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_246,plain,(
    ! [D_101,C_102,B_103,A_104] :
      ( r2_hidden(k1_funct_1(D_101,C_102),B_103)
      | k1_xboole_0 = B_103
      | ~ r2_hidden(C_102,A_104)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103)))
      | ~ v1_funct_2(D_101,A_104,B_103)
      | ~ v1_funct_1(D_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_259,plain,(
    ! [D_105,B_106] :
      ( r2_hidden(k1_funct_1(D_105,'#skF_5'),B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_106)))
      | ~ v1_funct_2(D_105,'#skF_3',B_106)
      | ~ v1_funct_1(D_105) ) ),
    inference(resolution,[status(thm)],[c_44,c_246])).

tff(c_262,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_259])).

tff(c_265,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_262])).

tff(c_266,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_265])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_271,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_266,c_6])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.25/1.29  
% 2.25/1.29  %Foreground sorts:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Background operators:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Foreground operators:
% 2.25/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.29  
% 2.25/1.31  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.25/1.31  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.25/1.31  tff(f_57, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.25/1.31  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.25/1.31  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.25/1.31  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.25/1.31  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.25/1.31  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.25/1.31  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.25/1.31  tff(c_42, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.31  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.31  tff(c_36, plain, (![A_39]: (k1_setfam_1(k1_tarski(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.25/1.31  tff(c_18, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.31  tff(c_93, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.31  tff(c_102, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=k1_setfam_1(k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_93])).
% 2.25/1.31  tff(c_105, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_102])).
% 2.25/1.31  tff(c_115, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.31  tff(c_124, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_105, c_115])).
% 2.25/1.31  tff(c_127, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 2.25/1.31  tff(c_32, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.31  tff(c_144, plain, (![B_38]: (k1_tarski(B_38)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_32])).
% 2.25/1.31  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.31  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.31  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.31  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.31  tff(c_246, plain, (![D_101, C_102, B_103, A_104]: (r2_hidden(k1_funct_1(D_101, C_102), B_103) | k1_xboole_0=B_103 | ~r2_hidden(C_102, A_104) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))) | ~v1_funct_2(D_101, A_104, B_103) | ~v1_funct_1(D_101))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.31  tff(c_259, plain, (![D_105, B_106]: (r2_hidden(k1_funct_1(D_105, '#skF_5'), B_106) | k1_xboole_0=B_106 | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_106))) | ~v1_funct_2(D_105, '#skF_3', B_106) | ~v1_funct_1(D_105))), inference(resolution, [status(thm)], [c_44, c_246])).
% 2.25/1.31  tff(c_262, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_259])).
% 2.25/1.31  tff(c_265, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_262])).
% 2.25/1.31  tff(c_266, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_144, c_265])).
% 2.25/1.31  tff(c_6, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.25/1.31  tff(c_271, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_266, c_6])).
% 2.25/1.31  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_271])).
% 2.25/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.31  
% 2.25/1.31  Inference rules
% 2.25/1.31  ----------------------
% 2.25/1.31  #Ref     : 0
% 2.25/1.31  #Sup     : 48
% 2.25/1.31  #Fact    : 0
% 2.25/1.31  #Define  : 0
% 2.25/1.31  #Split   : 0
% 2.25/1.31  #Chain   : 0
% 2.25/1.31  #Close   : 0
% 2.25/1.31  
% 2.25/1.31  Ordering : KBO
% 2.25/1.31  
% 2.25/1.31  Simplification rules
% 2.25/1.31  ----------------------
% 2.25/1.31  #Subsume      : 0
% 2.25/1.31  #Demod        : 7
% 2.25/1.31  #Tautology    : 37
% 2.25/1.31  #SimpNegUnit  : 2
% 2.25/1.31  #BackRed      : 1
% 2.25/1.31  
% 2.25/1.31  #Partial instantiations: 0
% 2.25/1.31  #Strategies tried      : 1
% 2.25/1.31  
% 2.25/1.31  Timing (in seconds)
% 2.25/1.31  ----------------------
% 2.25/1.31  Preprocessing        : 0.32
% 2.25/1.31  Parsing              : 0.16
% 2.25/1.31  CNF conversion       : 0.02
% 2.25/1.31  Main loop            : 0.19
% 2.25/1.31  Inferencing          : 0.07
% 2.25/1.31  Reduction            : 0.06
% 2.25/1.31  Demodulation         : 0.04
% 2.25/1.31  BG Simplification    : 0.02
% 2.25/1.31  Subsumption          : 0.03
% 2.25/1.31  Abstraction          : 0.02
% 2.25/1.31  MUC search           : 0.00
% 2.25/1.31  Cooper               : 0.00
% 2.25/1.31  Total                : 0.54
% 2.25/1.31  Index Insertion      : 0.00
% 2.25/1.31  Index Deletion       : 0.00
% 2.25/1.31  Index Matching       : 0.00
% 2.25/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
