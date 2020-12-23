%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:42 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 122 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_20,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_20])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_209,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_212,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_209])).

tff(c_215,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_212])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_216,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_36])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k6_domain_1(A_25,B_26),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_285,plain,(
    ! [B_66,A_67] :
      ( ~ v1_subset_1(B_66,A_67)
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_zfmisc_1(A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_296,plain,(
    ! [A_68,B_69] :
      ( ~ v1_subset_1(k6_domain_1(A_68,B_69),A_68)
      | v1_xboole_0(k6_domain_1(A_68,B_69))
      | ~ v1_zfmisc_1(A_68)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_28,c_285])).

tff(c_299,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_296])).

tff(c_301,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_215,c_216,c_299])).

tff(c_302,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_301])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_4])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.23  
% 2.16/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.24  
% 2.16/1.25  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.16/1.25  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.16/1.25  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.16/1.25  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.25  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.25  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.25  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.16/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.25  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.25  tff(c_81, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.25  tff(c_91, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_81])).
% 2.16/1.25  tff(c_20, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.25  tff(c_124, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_20])).
% 2.16/1.25  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.25  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.25  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.25  tff(c_209, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.25  tff(c_212, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_209])).
% 2.16/1.25  tff(c_215, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_212])).
% 2.16/1.25  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.25  tff(c_216, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_36])).
% 2.16/1.25  tff(c_28, plain, (![A_25, B_26]: (m1_subset_1(k6_domain_1(A_25, B_26), k1_zfmisc_1(A_25)) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.25  tff(c_285, plain, (![B_66, A_67]: (~v1_subset_1(B_66, A_67) | v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_zfmisc_1(A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.25  tff(c_296, plain, (![A_68, B_69]: (~v1_subset_1(k6_domain_1(A_68, B_69), A_68) | v1_xboole_0(k6_domain_1(A_68, B_69)) | ~v1_zfmisc_1(A_68) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_28, c_285])).
% 2.16/1.25  tff(c_299, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_296])).
% 2.16/1.25  tff(c_301, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_215, c_216, c_299])).
% 2.16/1.25  tff(c_302, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_301])).
% 2.16/1.25  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.25  tff(c_305, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_4])).
% 2.16/1.25  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_305])).
% 2.16/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  Inference rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Ref     : 0
% 2.16/1.25  #Sup     : 59
% 2.16/1.25  #Fact    : 0
% 2.16/1.25  #Define  : 0
% 2.16/1.25  #Split   : 1
% 2.16/1.25  #Chain   : 0
% 2.16/1.25  #Close   : 0
% 2.16/1.25  
% 2.16/1.25  Ordering : KBO
% 2.16/1.25  
% 2.16/1.25  Simplification rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Subsume      : 2
% 2.16/1.25  #Demod        : 19
% 2.16/1.25  #Tautology    : 42
% 2.16/1.25  #SimpNegUnit  : 8
% 2.16/1.25  #BackRed      : 3
% 2.16/1.25  
% 2.16/1.25  #Partial instantiations: 0
% 2.16/1.25  #Strategies tried      : 1
% 2.16/1.25  
% 2.16/1.25  Timing (in seconds)
% 2.16/1.25  ----------------------
% 2.16/1.25  Preprocessing        : 0.31
% 2.16/1.25  Parsing              : 0.17
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.18
% 2.16/1.25  Inferencing          : 0.07
% 2.16/1.25  Reduction            : 0.06
% 2.16/1.25  Demodulation         : 0.04
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.03
% 2.16/1.25  Abstraction          : 0.01
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.25  Total                : 0.51
% 2.16/1.25  Index Insertion      : 0.00
% 2.16/1.25  Index Deletion       : 0.00
% 2.16/1.25  Index Matching       : 0.00
% 2.16/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
