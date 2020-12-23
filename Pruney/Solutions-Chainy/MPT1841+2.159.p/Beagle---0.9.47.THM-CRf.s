%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:49 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 106 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 195 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_11] : ~ v1_subset_1(k2_subset_1(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [A_11] : ~ v1_subset_1(A_11,A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),B_28) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_108,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_104])).

tff(c_137,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k6_domain_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_137])).

tff(c_150,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_146])).

tff(c_151,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_150])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_151,c_18])).

tff(c_26,plain,(
    ! [B_20,A_18] :
      ( B_20 = A_18
      | ~ r1_tarski(A_18,B_20)
      | ~ v1_zfmisc_1(B_20)
      | v1_xboole_0(B_20)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_159,c_26])).

tff(c_165,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_162])).

tff(c_166,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_165])).

tff(c_167,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_181,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_181])).

tff(c_186,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_30,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_109,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_30])).

tff(c_190,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_109])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.25  
% 2.06/1.25  %Foreground sorts:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Background operators:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Foreground operators:
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.06/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.06/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.06/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.06/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.25  
% 2.16/1.27  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.16/1.27  tff(f_45, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.16/1.27  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.16/1.27  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.16/1.27  tff(f_88, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.27  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.27  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.27  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.16/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.27  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.27  tff(c_16, plain, (![A_11]: (~v1_subset_1(k2_subset_1(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.27  tff(c_35, plain, (![A_11]: (~v1_subset_1(A_11, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.16/1.27  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.27  tff(c_65, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.27  tff(c_69, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 2.16/1.27  tff(c_34, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.27  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.27  tff(c_32, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.27  tff(c_98, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.27  tff(c_104, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.16/1.27  tff(c_108, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_104])).
% 2.16/1.27  tff(c_137, plain, (![A_44, B_45]: (m1_subset_1(k6_domain_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.27  tff(c_146, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_137])).
% 2.16/1.27  tff(c_150, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_146])).
% 2.16/1.27  tff(c_151, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_34, c_150])).
% 2.16/1.27  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.27  tff(c_159, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_151, c_18])).
% 2.16/1.27  tff(c_26, plain, (![B_20, A_18]: (B_20=A_18 | ~r1_tarski(A_18, B_20) | ~v1_zfmisc_1(B_20) | v1_xboole_0(B_20) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.27  tff(c_162, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_159, c_26])).
% 2.16/1.27  tff(c_165, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_162])).
% 2.16/1.27  tff(c_166, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_165])).
% 2.16/1.27  tff(c_167, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.16/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.27  tff(c_181, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_2])).
% 2.16/1.27  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_181])).
% 2.16/1.27  tff(c_186, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_166])).
% 2.16/1.27  tff(c_30, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.27  tff(c_109, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_30])).
% 2.16/1.27  tff(c_190, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_109])).
% 2.16/1.27  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_190])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 31
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 1
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 0
% 2.16/1.27  #Demod        : 10
% 2.16/1.27  #Tautology    : 18
% 2.16/1.27  #SimpNegUnit  : 6
% 2.16/1.27  #BackRed      : 5
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.27  Preprocessing        : 0.32
% 2.16/1.27  Parsing              : 0.17
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.15
% 2.16/1.27  Inferencing          : 0.06
% 2.16/1.27  Reduction            : 0.05
% 2.16/1.27  Demodulation         : 0.03
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.02
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.49
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
