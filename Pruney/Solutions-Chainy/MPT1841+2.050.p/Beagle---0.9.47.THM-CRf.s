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
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 129 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 257 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_61,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_56,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),B_28) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_93,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_107,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_102])).

tff(c_113,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k6_domain_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_113])).

tff(c_126,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_127,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_126])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_164,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_zfmisc_1(B_49)
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_170,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_135,c_164])).

tff(c_177,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_170])).

tff(c_178,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_177])).

tff(c_181,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_63,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_184,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_66])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_184])).

tff(c_191,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_108,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_32])).

tff(c_195,plain,(
    v1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_108])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1('#skF_1'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    ! [A_12] : r1_tarski('#skF_1'(A_12),A_12) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_477,plain,(
    ! [A_60] :
      ( '#skF_1'(A_60) = A_60
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60)
      | v1_xboole_0('#skF_1'(A_60)) ) ),
    inference(resolution,[status(thm)],[c_91,c_164])).

tff(c_16,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_1'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | v1_subset_1(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_1'(A_12))
      | v1_subset_1('#skF_1'(A_12),A_12)
      | v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_163,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_1'(A_12))
      | v1_xboole_0(A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_155])).

tff(c_508,plain,(
    ! [A_62] :
      ( '#skF_1'(A_62) = A_62
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_477,c_163])).

tff(c_511,plain,
    ( '#skF_1'('#skF_2') = '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_508])).

tff(c_514,plain,(
    '#skF_1'('#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_511])).

tff(c_530,plain,(
    ~ v1_subset_1('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_16])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.44  
% 2.37/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.44  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.37/1.44  
% 2.37/1.44  %Foreground sorts:
% 2.37/1.44  
% 2.37/1.44  
% 2.37/1.44  %Background operators:
% 2.37/1.44  
% 2.37/1.44  
% 2.37/1.44  %Foreground operators:
% 2.37/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.37/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.37/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.37/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.44  
% 2.37/1.45  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.37/1.45  tff(f_43, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.37/1.45  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.37/1.45  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.37/1.45  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.37/1.45  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.37/1.45  tff(f_92, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.37/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.45  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.37/1.45  tff(f_61, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.37/1.45  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.37/1.45  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.37/1.45  tff(c_56, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.45  tff(c_60, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_56])).
% 2.37/1.45  tff(c_36, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.45  tff(c_30, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.45  tff(c_34, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.45  tff(c_93, plain, (![A_41, B_42]: (k6_domain_1(A_41, B_42)=k1_tarski(B_42) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.37/1.45  tff(c_102, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_93])).
% 2.37/1.45  tff(c_107, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_102])).
% 2.37/1.45  tff(c_113, plain, (![A_43, B_44]: (m1_subset_1(k6_domain_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.45  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_107, c_113])).
% 2.37/1.45  tff(c_126, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_122])).
% 2.37/1.45  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_126])).
% 2.37/1.45  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.45  tff(c_135, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_127, c_20])).
% 2.37/1.45  tff(c_164, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(A_50, B_49) | ~v1_zfmisc_1(B_49) | v1_xboole_0(B_49) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.37/1.45  tff(c_170, plain, (k1_tarski('#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_135, c_164])).
% 2.37/1.45  tff(c_177, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_170])).
% 2.37/1.45  tff(c_178, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_177])).
% 2.37/1.45  tff(c_181, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_178])).
% 2.37/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.45  tff(c_63, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.45  tff(c_66, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_63])).
% 2.37/1.45  tff(c_184, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_181, c_66])).
% 2.37/1.45  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_184])).
% 2.37/1.45  tff(c_191, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_178])).
% 2.37/1.45  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.37/1.45  tff(c_108, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_32])).
% 2.37/1.45  tff(c_195, plain, (v1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_108])).
% 2.37/1.45  tff(c_18, plain, (![A_12]: (m1_subset_1('#skF_1'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.45  tff(c_83, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.45  tff(c_91, plain, (![A_12]: (r1_tarski('#skF_1'(A_12), A_12))), inference(resolution, [status(thm)], [c_18, c_83])).
% 2.37/1.45  tff(c_477, plain, (![A_60]: ('#skF_1'(A_60)=A_60 | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60) | v1_xboole_0('#skF_1'(A_60)))), inference(resolution, [status(thm)], [c_91, c_164])).
% 2.37/1.45  tff(c_16, plain, (![A_12]: (~v1_subset_1('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.45  tff(c_143, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | v1_subset_1(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.45  tff(c_155, plain, (![A_12]: (~v1_xboole_0('#skF_1'(A_12)) | v1_subset_1('#skF_1'(A_12), A_12) | v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_18, c_143])).
% 2.37/1.45  tff(c_163, plain, (![A_12]: (~v1_xboole_0('#skF_1'(A_12)) | v1_xboole_0(A_12))), inference(negUnitSimplification, [status(thm)], [c_16, c_155])).
% 2.37/1.45  tff(c_508, plain, (![A_62]: ('#skF_1'(A_62)=A_62 | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_477, c_163])).
% 2.37/1.45  tff(c_511, plain, ('#skF_1'('#skF_2')='#skF_2' | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_508])).
% 2.37/1.45  tff(c_514, plain, ('#skF_1'('#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_511])).
% 2.37/1.45  tff(c_530, plain, (~v1_subset_1('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_514, c_16])).
% 2.37/1.45  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_530])).
% 2.37/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.45  
% 2.37/1.45  Inference rules
% 2.37/1.45  ----------------------
% 2.37/1.45  #Ref     : 0
% 2.37/1.45  #Sup     : 105
% 2.37/1.45  #Fact    : 0
% 2.37/1.45  #Define  : 0
% 2.37/1.45  #Split   : 5
% 2.37/1.45  #Chain   : 0
% 2.37/1.45  #Close   : 0
% 2.37/1.45  
% 2.37/1.45  Ordering : KBO
% 2.37/1.45  
% 2.37/1.45  Simplification rules
% 2.37/1.45  ----------------------
% 2.37/1.45  #Subsume      : 9
% 2.37/1.45  #Demod        : 61
% 2.37/1.46  #Tautology    : 50
% 2.37/1.46  #SimpNegUnit  : 27
% 2.37/1.46  #BackRed      : 9
% 2.37/1.46  
% 2.37/1.46  #Partial instantiations: 0
% 2.37/1.46  #Strategies tried      : 1
% 2.37/1.46  
% 2.37/1.46  Timing (in seconds)
% 2.37/1.46  ----------------------
% 2.37/1.46  Preprocessing        : 0.38
% 2.37/1.46  Parsing              : 0.20
% 2.37/1.46  CNF conversion       : 0.02
% 2.37/1.46  Main loop            : 0.28
% 2.37/1.46  Inferencing          : 0.10
% 2.37/1.46  Reduction            : 0.09
% 2.37/1.46  Demodulation         : 0.06
% 2.37/1.46  BG Simplification    : 0.02
% 2.37/1.46  Subsumption          : 0.05
% 2.37/1.46  Abstraction          : 0.02
% 2.37/1.46  MUC search           : 0.00
% 2.37/1.46  Cooper               : 0.00
% 2.37/1.46  Total                : 0.69
% 2.37/1.46  Index Insertion      : 0.00
% 2.37/1.46  Index Deletion       : 0.00
% 2.37/1.46  Index Matching       : 0.00
% 2.37/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
