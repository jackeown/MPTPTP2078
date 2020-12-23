%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:31 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 104 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : ~ v1_xboole_0(k2_enumset1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : ~ v1_xboole_0(k2_enumset1(A_7,B_8,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_36,B_37,C_38] : ~ v1_xboole_0(k1_enumset1(A_36,B_37,C_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_66,plain,(
    ! [A_39,B_40] : ~ v1_xboole_0(k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_68,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_18,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ! [A_34,B_35] :
      ( k6_domain_1(A_34,B_35) = k1_tarski(B_35)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_62,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_59])).

tff(c_20,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_75,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k6_domain_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_75])).

tff(c_88,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_84])).

tff(c_89,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_88])).

tff(c_100,plain,(
    ! [B_44,A_45] :
      ( ~ v1_subset_1(B_44,A_45)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_zfmisc_1(A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_100])).

tff(c_109,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_70,c_103])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_68,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.86/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.86/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.86/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.18  
% 1.94/1.19  tff(f_81, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.94/1.19  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.94/1.19  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.94/1.19  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.94/1.19  tff(f_34, axiom, (![A, B, C, D]: ~v1_xboole_0(k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_subset_1)).
% 1.94/1.19  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.94/1.19  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.94/1.19  tff(f_69, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.94/1.19  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.19  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.19  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.19  tff(c_45, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.19  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (~v1_xboole_0(k2_enumset1(A_7, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.94/1.19  tff(c_63, plain, (![A_36, B_37, C_38]: (~v1_xboole_0(k1_enumset1(A_36, B_37, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_8])).
% 1.94/1.19  tff(c_66, plain, (![A_39, B_40]: (~v1_xboole_0(k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63])).
% 1.94/1.19  tff(c_68, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 1.94/1.19  tff(c_18, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.19  tff(c_22, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.19  tff(c_56, plain, (![A_34, B_35]: (k6_domain_1(A_34, B_35)=k1_tarski(B_35) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.19  tff(c_59, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_56])).
% 1.94/1.19  tff(c_62, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_59])).
% 1.94/1.19  tff(c_20, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.94/1.19  tff(c_70, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20])).
% 1.94/1.19  tff(c_75, plain, (![A_42, B_43]: (m1_subset_1(k6_domain_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.19  tff(c_84, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62, c_75])).
% 1.94/1.19  tff(c_88, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_84])).
% 1.94/1.19  tff(c_89, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_24, c_88])).
% 1.94/1.19  tff(c_100, plain, (![B_44, A_45]: (~v1_subset_1(B_44, A_45) | v1_xboole_0(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_zfmisc_1(A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.94/1.19  tff(c_103, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_89, c_100])).
% 1.94/1.19  tff(c_109, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_70, c_103])).
% 1.94/1.19  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_68, c_109])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 19
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 1
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 1
% 1.94/1.19  #Demod        : 4
% 1.94/1.19  #Tautology    : 9
% 1.94/1.19  #SimpNegUnit  : 4
% 1.94/1.19  #BackRed      : 1
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.19  Preprocessing        : 0.30
% 1.94/1.19  Parsing              : 0.16
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.13
% 1.94/1.19  Inferencing          : 0.05
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.02
% 1.94/1.19  BG Simplification    : 0.01
% 1.94/1.19  Subsumption          : 0.02
% 1.94/1.19  Abstraction          : 0.01
% 1.94/1.19  MUC search           : 0.00
% 1.94/1.19  Cooper               : 0.00
% 1.94/1.19  Total                : 0.46
% 1.94/1.19  Index Insertion      : 0.00
% 1.94/1.19  Index Deletion       : 0.00
% 1.94/1.19  Index Matching       : 0.00
% 1.94/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
