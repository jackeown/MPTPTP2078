%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:38 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_80,plain,(
    ! [A_45] : k2_tarski(A_45,A_45) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [A_45] : r2_hidden(A_45,k1_tarski(A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_16])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k2_xboole_0(A_47,B_48)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_207,plain,(
    ! [B_61,A_62] :
      ( ~ r2_hidden(B_61,A_62)
      | k4_xboole_0(A_62,k1_tarski(B_61)) != A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,(
    ! [B_61] :
      ( ~ r2_hidden(B_61,k1_tarski(B_61))
      | k1_tarski(B_61) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_207])).

tff(c_217,plain,(
    ! [B_61] : k1_tarski(B_61) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_214])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_269,plain,(
    ! [A_77,B_78] :
      ( k6_domain_1(A_77,B_78) = k1_tarski(B_78)
      | ~ m1_subset_1(B_78,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_272,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_269])).

tff(c_275,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_272])).

tff(c_54,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_276,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_54])).

tff(c_281,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k6_domain_1(A_79,B_80),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_290,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_281])).

tff(c_294,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_290])).

tff(c_295,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_294])).

tff(c_307,plain,(
    ! [B_81,A_82] :
      ( ~ v1_subset_1(B_81,A_82)
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_zfmisc_1(A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_310,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_295,c_307])).

tff(c_316,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_276,c_310])).

tff(c_317,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_316])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_321,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.35  
% 2.26/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.35  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.26/1.35  
% 2.26/1.35  %Foreground sorts:
% 2.26/1.35  
% 2.26/1.35  
% 2.26/1.35  %Background operators:
% 2.26/1.35  
% 2.26/1.35  
% 2.26/1.35  %Foreground operators:
% 2.26/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.35  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.26/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.26/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.26/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.26/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.35  
% 2.26/1.38  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.38  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.26/1.38  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.26/1.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.26/1.38  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.26/1.38  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.26/1.38  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.26/1.38  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.26/1.38  tff(f_97, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.26/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.26/1.38  tff(c_80, plain, (![A_45]: (k2_tarski(A_45, A_45)=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.38  tff(c_16, plain, (![D_14, B_10]: (r2_hidden(D_14, k2_tarski(D_14, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.38  tff(c_86, plain, (![A_45]: (r2_hidden(A_45, k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_16])).
% 2.26/1.38  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.38  tff(c_97, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k2_xboole_0(A_47, B_48))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.38  tff(c_104, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_97])).
% 2.26/1.38  tff(c_207, plain, (![B_61, A_62]: (~r2_hidden(B_61, A_62) | k4_xboole_0(A_62, k1_tarski(B_61))!=A_62)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.38  tff(c_214, plain, (![B_61]: (~r2_hidden(B_61, k1_tarski(B_61)) | k1_tarski(B_61)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_207])).
% 2.26/1.38  tff(c_217, plain, (![B_61]: (k1_tarski(B_61)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_214])).
% 2.26/1.38  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.38  tff(c_52, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.38  tff(c_56, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.38  tff(c_269, plain, (![A_77, B_78]: (k6_domain_1(A_77, B_78)=k1_tarski(B_78) | ~m1_subset_1(B_78, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.38  tff(c_272, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_269])).
% 2.26/1.38  tff(c_275, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_272])).
% 2.26/1.38  tff(c_54, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.26/1.38  tff(c_276, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_54])).
% 2.26/1.38  tff(c_281, plain, (![A_79, B_80]: (m1_subset_1(k6_domain_1(A_79, B_80), k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.26/1.38  tff(c_290, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_281])).
% 2.26/1.38  tff(c_294, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_290])).
% 2.26/1.38  tff(c_295, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_294])).
% 2.26/1.38  tff(c_307, plain, (![B_81, A_82]: (~v1_subset_1(B_81, A_82) | v1_xboole_0(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_zfmisc_1(A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.38  tff(c_310, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_295, c_307])).
% 2.26/1.38  tff(c_316, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_276, c_310])).
% 2.26/1.38  tff(c_317, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_316])).
% 2.26/1.38  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.38  tff(c_321, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_317, c_4])).
% 2.26/1.38  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_321])).
% 2.26/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.38  
% 2.26/1.38  Inference rules
% 2.26/1.38  ----------------------
% 2.26/1.38  #Ref     : 0
% 2.26/1.38  #Sup     : 59
% 2.26/1.38  #Fact    : 0
% 2.26/1.38  #Define  : 0
% 2.26/1.38  #Split   : 1
% 2.26/1.38  #Chain   : 0
% 2.26/1.38  #Close   : 0
% 2.26/1.38  
% 2.26/1.38  Ordering : KBO
% 2.26/1.38  
% 2.26/1.38  Simplification rules
% 2.26/1.38  ----------------------
% 2.26/1.38  #Subsume      : 1
% 2.26/1.38  #Demod        : 12
% 2.26/1.38  #Tautology    : 43
% 2.26/1.38  #SimpNegUnit  : 4
% 2.26/1.38  #BackRed      : 1
% 2.26/1.38  
% 2.26/1.38  #Partial instantiations: 0
% 2.26/1.38  #Strategies tried      : 1
% 2.26/1.38  
% 2.26/1.38  Timing (in seconds)
% 2.26/1.38  ----------------------
% 2.51/1.38  Preprocessing        : 0.34
% 2.51/1.38  Parsing              : 0.17
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.25
% 2.51/1.38  Inferencing          : 0.09
% 2.51/1.38  Reduction            : 0.08
% 2.51/1.38  Demodulation         : 0.06
% 2.51/1.38  BG Simplification    : 0.02
% 2.51/1.38  Subsumption          : 0.05
% 2.51/1.38  Abstraction          : 0.02
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.64
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
