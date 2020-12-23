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
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   62 (  69 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 103 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : ~ v1_xboole_0(k2_enumset1(A,B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_18] : ~ v1_subset_1(k2_subset_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41,plain,(
    ! [A_18] : ~ v1_subset_1(A_18,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : ~ v1_xboole_0(k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_96,plain,(
    ! [A_57,B_58,C_59] : ~ v1_xboole_0(k1_enumset1(A_57,B_58,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_99,plain,(
    ! [A_60,B_61] : ~ v1_xboole_0(k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_101,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_79,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k1_tarski(A_50),k1_zfmisc_1(B_51))
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_79,c_22])).

tff(c_146,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(A_72,B_71)
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_149,plain,(
    ! [A_50,B_51] :
      ( k1_tarski(A_50) = B_51
      | ~ v1_zfmisc_1(B_51)
      | v1_xboole_0(B_51)
      | v1_xboole_0(k1_tarski(A_50))
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_83,c_146])).

tff(c_153,plain,(
    ! [A_73,B_74] :
      ( k1_tarski(A_73) = B_74
      | ~ v1_zfmisc_1(B_74)
      | v1_xboole_0(B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_149])).

tff(c_158,plain,(
    ! [A_75,B_76] :
      ( k1_tarski(A_75) = B_76
      | ~ v1_zfmisc_1(B_76)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_20,c_153])).

tff(c_167,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_172,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_167])).

tff(c_173,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_172])).

tff(c_118,plain,(
    ! [A_69,B_70] :
      ( k6_domain_1(A_69,B_70) = k1_tarski(B_70)
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_127,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_118])).

tff(c_132,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_127])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_133,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_36])).

tff(c_174,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_133])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:59:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.09/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.09/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.09/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.09/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.28  
% 2.09/1.29  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.09/1.29  tff(f_55, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.09/1.29  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.09/1.29  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.09/1.29  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.29  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.29  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.09/1.29  tff(f_40, axiom, (![A, B, C, D]: ~v1_xboole_0(k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_subset_1)).
% 2.09/1.29  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.09/1.29  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.29  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.09/1.29  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.09/1.29  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.29  tff(c_18, plain, (![A_18]: (~v1_subset_1(k2_subset_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.29  tff(c_41, plain, (![A_18]: (~v1_subset_1(A_18, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.09/1.29  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.09/1.29  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.09/1.29  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.09/1.29  tff(c_20, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.29  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.29  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.29  tff(c_85, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.29  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (~v1_xboole_0(k2_enumset1(A_9, B_10, C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.29  tff(c_96, plain, (![A_57, B_58, C_59]: (~v1_xboole_0(k1_enumset1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_12])).
% 2.09/1.29  tff(c_99, plain, (![A_60, B_61]: (~v1_xboole_0(k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 2.09/1.29  tff(c_101, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_99])).
% 2.09/1.29  tff(c_79, plain, (![A_50, B_51]: (m1_subset_1(k1_tarski(A_50), k1_zfmisc_1(B_51)) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.29  tff(c_22, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.09/1.29  tff(c_83, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(resolution, [status(thm)], [c_79, c_22])).
% 2.09/1.29  tff(c_146, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(A_72, B_71) | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.09/1.29  tff(c_149, plain, (![A_50, B_51]: (k1_tarski(A_50)=B_51 | ~v1_zfmisc_1(B_51) | v1_xboole_0(B_51) | v1_xboole_0(k1_tarski(A_50)) | ~r2_hidden(A_50, B_51))), inference(resolution, [status(thm)], [c_83, c_146])).
% 2.09/1.29  tff(c_153, plain, (![A_73, B_74]: (k1_tarski(A_73)=B_74 | ~v1_zfmisc_1(B_74) | v1_xboole_0(B_74) | ~r2_hidden(A_73, B_74))), inference(negUnitSimplification, [status(thm)], [c_101, c_149])).
% 2.09/1.29  tff(c_158, plain, (![A_75, B_76]: (k1_tarski(A_75)=B_76 | ~v1_zfmisc_1(B_76) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(resolution, [status(thm)], [c_20, c_153])).
% 2.09/1.29  tff(c_167, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_158])).
% 2.09/1.29  tff(c_172, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_167])).
% 2.09/1.29  tff(c_173, plain, (k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_172])).
% 2.09/1.29  tff(c_118, plain, (![A_69, B_70]: (k6_domain_1(A_69, B_70)=k1_tarski(B_70) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.09/1.29  tff(c_127, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_118])).
% 2.09/1.29  tff(c_132, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_127])).
% 2.09/1.29  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.09/1.29  tff(c_133, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_36])).
% 2.09/1.29  tff(c_174, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_133])).
% 2.09/1.29  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_174])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 28
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 0
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 3
% 2.09/1.29  #Demod        : 5
% 2.09/1.29  #Tautology    : 11
% 2.09/1.29  #SimpNegUnit  : 4
% 2.09/1.29  #BackRed      : 3
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.30  Preprocessing        : 0.33
% 2.09/1.30  Parsing              : 0.18
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.15
% 2.09/1.30  Inferencing          : 0.06
% 2.09/1.30  Reduction            : 0.05
% 2.09/1.30  Demodulation         : 0.03
% 2.09/1.30  BG Simplification    : 0.02
% 2.09/1.30  Subsumption          : 0.02
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.52
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
