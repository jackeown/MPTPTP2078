%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 115 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ( A != k1_xboole_0
                   => m1_subset_1(k2_enumset1(B,C,D,E),k1_zfmisc_1(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_62,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_59])).

tff(c_22,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_10,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [B_49,C_47,A_48,E_46,D_50] :
      ( m1_subset_1(k2_enumset1(B_49,C_47,D_50,E_46),k1_zfmisc_1(A_48))
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(E_46,A_48)
      | ~ m1_subset_1(D_50,A_48)
      | ~ m1_subset_1(C_47,A_48)
      | ~ m1_subset_1(B_49,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_51,B_52,C_53,A_54] :
      ( m1_subset_1(k1_enumset1(A_51,B_52,C_53),k1_zfmisc_1(A_54))
      | k1_xboole_0 = A_54
      | ~ m1_subset_1(C_53,A_54)
      | ~ m1_subset_1(B_52,A_54)
      | ~ m1_subset_1(A_51,A_54)
      | ~ m1_subset_1(A_51,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_116,plain,(
    ! [A_64,B_65,A_66] :
      ( m1_subset_1(k2_tarski(A_64,B_65),k1_zfmisc_1(A_66))
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(B_65,A_66)
      | ~ m1_subset_1(A_64,A_66)
      | ~ m1_subset_1(A_64,A_66)
      | ~ m1_subset_1(A_64,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_132,plain,(
    ! [A_67,A_68] :
      ( m1_subset_1(k1_tarski(A_67),k1_zfmisc_1(A_68))
      | k1_xboole_0 = A_68
      | ~ m1_subset_1(A_67,A_68)
      | ~ m1_subset_1(A_67,A_68)
      | ~ m1_subset_1(A_67,A_68)
      | ~ m1_subset_1(A_67,A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_116])).

tff(c_18,plain,(
    ! [B_31,A_29] :
      ( ~ v1_subset_1(B_31,A_29)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_29))
      | ~ v1_zfmisc_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_135,plain,(
    ! [A_67,A_68] :
      ( ~ v1_subset_1(k1_tarski(A_67),A_68)
      | v1_xboole_0(k1_tarski(A_67))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68)
      | k1_xboole_0 = A_68
      | ~ m1_subset_1(A_67,A_68) ) ),
    inference(resolution,[status(thm)],[c_132,c_18])).

tff(c_147,plain,(
    ! [A_69,A_70] :
      ( ~ v1_subset_1(k1_tarski(A_69),A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | k1_xboole_0 = A_70
      | ~ m1_subset_1(A_69,A_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_135])).

tff(c_150,plain,
    ( ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_147])).

tff(c_153,plain,
    ( v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_150])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_153])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_163,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.15/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.15/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.26  
% 2.15/1.27  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.15/1.27  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.15/1.27  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.15/1.27  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.27  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.27  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.15/1.27  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_enumset1(B, C, D, E), k1_zfmisc_1(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_subset_1)).
% 2.15/1.27  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.15/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.27  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.27  tff(c_24, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.27  tff(c_20, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.27  tff(c_56, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.27  tff(c_59, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_56])).
% 2.15/1.27  tff(c_62, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_59])).
% 2.15/1.27  tff(c_22, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.15/1.27  tff(c_63, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 2.15/1.27  tff(c_10, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.27  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.15/1.27  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.15/1.27  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.27  tff(c_69, plain, (![B_49, C_47, A_48, E_46, D_50]: (m1_subset_1(k2_enumset1(B_49, C_47, D_50, E_46), k1_zfmisc_1(A_48)) | k1_xboole_0=A_48 | ~m1_subset_1(E_46, A_48) | ~m1_subset_1(D_50, A_48) | ~m1_subset_1(C_47, A_48) | ~m1_subset_1(B_49, A_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.27  tff(c_85, plain, (![A_51, B_52, C_53, A_54]: (m1_subset_1(k1_enumset1(A_51, B_52, C_53), k1_zfmisc_1(A_54)) | k1_xboole_0=A_54 | ~m1_subset_1(C_53, A_54) | ~m1_subset_1(B_52, A_54) | ~m1_subset_1(A_51, A_54) | ~m1_subset_1(A_51, A_54))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 2.15/1.27  tff(c_116, plain, (![A_64, B_65, A_66]: (m1_subset_1(k2_tarski(A_64, B_65), k1_zfmisc_1(A_66)) | k1_xboole_0=A_66 | ~m1_subset_1(B_65, A_66) | ~m1_subset_1(A_64, A_66) | ~m1_subset_1(A_64, A_66) | ~m1_subset_1(A_64, A_66))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 2.15/1.27  tff(c_132, plain, (![A_67, A_68]: (m1_subset_1(k1_tarski(A_67), k1_zfmisc_1(A_68)) | k1_xboole_0=A_68 | ~m1_subset_1(A_67, A_68) | ~m1_subset_1(A_67, A_68) | ~m1_subset_1(A_67, A_68) | ~m1_subset_1(A_67, A_68))), inference(superposition, [status(thm), theory('equality')], [c_4, c_116])).
% 2.15/1.27  tff(c_18, plain, (![B_31, A_29]: (~v1_subset_1(B_31, A_29) | v1_xboole_0(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_29)) | ~v1_zfmisc_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.27  tff(c_135, plain, (![A_67, A_68]: (~v1_subset_1(k1_tarski(A_67), A_68) | v1_xboole_0(k1_tarski(A_67)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68) | k1_xboole_0=A_68 | ~m1_subset_1(A_67, A_68))), inference(resolution, [status(thm)], [c_132, c_18])).
% 2.15/1.27  tff(c_147, plain, (![A_69, A_70]: (~v1_subset_1(k1_tarski(A_69), A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | k1_xboole_0=A_70 | ~m1_subset_1(A_69, A_70))), inference(negUnitSimplification, [status(thm)], [c_10, c_135])).
% 2.15/1.27  tff(c_150, plain, (~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_63, c_147])).
% 2.15/1.27  tff(c_153, plain, (v1_xboole_0('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_150])).
% 2.15/1.27  tff(c_154, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_153])).
% 2.15/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.15/1.27  tff(c_163, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2])).
% 2.15/1.27  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_163])).
% 2.15/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  Inference rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Ref     : 0
% 2.15/1.27  #Sup     : 28
% 2.15/1.27  #Fact    : 0
% 2.15/1.27  #Define  : 0
% 2.15/1.27  #Split   : 0
% 2.15/1.27  #Chain   : 0
% 2.15/1.27  #Close   : 0
% 2.15/1.27  
% 2.15/1.27  Ordering : KBO
% 2.15/1.27  
% 2.15/1.27  Simplification rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Subsume      : 3
% 2.15/1.27  #Demod        : 13
% 2.15/1.27  #Tautology    : 8
% 2.15/1.27  #SimpNegUnit  : 4
% 2.15/1.27  #BackRed      : 10
% 2.15/1.27  
% 2.15/1.27  #Partial instantiations: 0
% 2.15/1.27  #Strategies tried      : 1
% 2.15/1.27  
% 2.15/1.27  Timing (in seconds)
% 2.15/1.27  ----------------------
% 2.15/1.27  Preprocessing        : 0.30
% 2.15/1.27  Parsing              : 0.16
% 2.15/1.27  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.17
% 2.15/1.27  Inferencing          : 0.07
% 2.15/1.27  Reduction            : 0.05
% 2.15/1.27  Demodulation         : 0.03
% 2.15/1.27  BG Simplification    : 0.02
% 2.15/1.27  Subsumption          : 0.03
% 2.15/1.27  Abstraction          : 0.01
% 2.15/1.27  MUC search           : 0.00
% 2.15/1.27  Cooper               : 0.00
% 2.15/1.27  Total                : 0.50
% 2.15/1.27  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
