%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 107 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : ~ v1_xboole_0(k3_enumset1(A,B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_49,B_50,C_51,D_52] : k3_enumset1(A_49,A_49,B_50,C_51,D_52) = k2_enumset1(A_49,B_50,C_51,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : ~ v1_xboole_0(k3_enumset1(A_17,B_18,C_19,D_20,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [A_55,B_56,C_57,D_58] : ~ v1_xboole_0(k2_enumset1(A_55,B_56,C_57,D_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_16])).

tff(c_119,plain,(
    ! [A_59,B_60,C_61] : ~ v1_xboole_0(k1_enumset1(A_59,B_60,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_116])).

tff(c_192,plain,(
    ! [A_74,B_75] : ~ v1_xboole_0(k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_194,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_192])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_74,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_71])).

tff(c_28,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_75,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_91,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k6_domain_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_91])).

tff(c_104,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_105,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_104])).

tff(c_223,plain,(
    ! [B_82,A_83] :
      ( ~ v1_subset_1(B_82,A_83)
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_zfmisc_1(A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_229,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_105,c_223])).

tff(c_238,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75,c_229])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_194,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.24  
% 2.36/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.25  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.36/1.25  
% 2.36/1.25  %Foreground sorts:
% 2.36/1.25  
% 2.36/1.25  
% 2.36/1.25  %Background operators:
% 2.36/1.25  
% 2.36/1.25  
% 2.36/1.25  %Foreground operators:
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.36/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.36/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.36/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.25  
% 2.36/1.26  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.36/1.26  tff(f_32, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.26  tff(f_34, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.26  tff(f_36, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.36/1.26  tff(f_38, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.36/1.26  tff(f_43, axiom, (![A, B, C, D, E]: ~v1_xboole_0(k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_subset_1)).
% 2.36/1.26  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.36/1.26  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.36/1.26  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.36/1.26  tff(c_32, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.26  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.26  tff(c_8, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.26  tff(c_10, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.26  tff(c_80, plain, (![A_49, B_50, C_51, D_52]: (k3_enumset1(A_49, A_49, B_50, C_51, D_52)=k2_enumset1(A_49, B_50, C_51, D_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.26  tff(c_16, plain, (![E_21, D_20, C_19, B_18, A_17]: (~v1_xboole_0(k3_enumset1(A_17, B_18, C_19, D_20, E_21)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.26  tff(c_116, plain, (![A_55, B_56, C_57, D_58]: (~v1_xboole_0(k2_enumset1(A_55, B_56, C_57, D_58)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_16])).
% 2.36/1.26  tff(c_119, plain, (![A_59, B_60, C_61]: (~v1_xboole_0(k1_enumset1(A_59, B_60, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_116])).
% 2.36/1.26  tff(c_192, plain, (![A_74, B_75]: (~v1_xboole_0(k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_119])).
% 2.36/1.26  tff(c_194, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_192])).
% 2.36/1.26  tff(c_26, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.26  tff(c_30, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.26  tff(c_68, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.26  tff(c_71, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.36/1.26  tff(c_74, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_71])).
% 2.36/1.26  tff(c_28, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.26  tff(c_75, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_28])).
% 2.36/1.26  tff(c_91, plain, (![A_53, B_54]: (m1_subset_1(k6_domain_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.26  tff(c_100, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_91])).
% 2.36/1.26  tff(c_104, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_100])).
% 2.36/1.26  tff(c_105, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_32, c_104])).
% 2.36/1.26  tff(c_223, plain, (![B_82, A_83]: (~v1_subset_1(B_82, A_83) | v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_zfmisc_1(A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.36/1.26  tff(c_229, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_105, c_223])).
% 2.36/1.26  tff(c_238, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75, c_229])).
% 2.36/1.26  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_194, c_238])).
% 2.36/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.26  
% 2.36/1.26  Inference rules
% 2.36/1.26  ----------------------
% 2.36/1.26  #Ref     : 0
% 2.36/1.26  #Sup     : 45
% 2.36/1.26  #Fact    : 0
% 2.36/1.27  #Define  : 0
% 2.36/1.27  #Split   : 1
% 2.36/1.27  #Chain   : 0
% 2.36/1.27  #Close   : 0
% 2.36/1.27  
% 2.36/1.27  Ordering : KBO
% 2.36/1.27  
% 2.36/1.27  Simplification rules
% 2.36/1.27  ----------------------
% 2.36/1.27  #Subsume      : 3
% 2.36/1.27  #Demod        : 15
% 2.36/1.27  #Tautology    : 24
% 2.36/1.27  #SimpNegUnit  : 8
% 2.36/1.27  #BackRed      : 3
% 2.36/1.27  
% 2.36/1.27  #Partial instantiations: 0
% 2.36/1.27  #Strategies tried      : 1
% 2.36/1.27  
% 2.36/1.27  Timing (in seconds)
% 2.36/1.27  ----------------------
% 2.36/1.27  Preprocessing        : 0.31
% 2.36/1.27  Parsing              : 0.17
% 2.36/1.27  CNF conversion       : 0.02
% 2.36/1.27  Main loop            : 0.19
% 2.36/1.27  Inferencing          : 0.08
% 2.36/1.27  Reduction            : 0.06
% 2.36/1.27  Demodulation         : 0.04
% 2.36/1.27  BG Simplification    : 0.02
% 2.36/1.27  Subsumption          : 0.03
% 2.36/1.27  Abstraction          : 0.01
% 2.36/1.27  MUC search           : 0.00
% 2.36/1.27  Cooper               : 0.00
% 2.36/1.27  Total                : 0.54
% 2.36/1.27  Index Insertion      : 0.00
% 2.36/1.27  Index Deletion       : 0.00
% 2.36/1.27  Index Matching       : 0.00
% 2.36/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
