%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 164 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_22,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_tarski(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_248,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_257,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_248])).

tff(c_262,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_257])).

tff(c_576,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k6_domain_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_585,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_576])).

tff(c_589,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_585])).

tff(c_590,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_589])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_598,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_590,c_30])).

tff(c_38,plain,(
    ! [B_30,A_28] :
      ( B_30 = A_28
      | ~ r1_tarski(A_28,B_30)
      | ~ v1_zfmisc_1(B_30)
      | v1_xboole_0(B_30)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_601,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_598,c_38])).

tff(c_611,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_601])).

tff(c_612,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_46,c_611])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_263,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_42])).

tff(c_618,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_263])).

tff(c_28,plain,(
    ! [A_20] : m1_subset_1('#skF_3'(A_20),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_76,plain,(
    ! [A_20] : r1_tarski('#skF_3'(A_20),A_20) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_448,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(A_77,B_76)
      | ~ v1_zfmisc_1(B_76)
      | v1_xboole_0(B_76)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4360,plain,(
    ! [A_160] :
      ( '#skF_3'(A_160) = A_160
      | ~ v1_zfmisc_1(A_160)
      | v1_xboole_0(A_160)
      | v1_xboole_0('#skF_3'(A_160)) ) ),
    inference(resolution,[status(thm)],[c_76,c_448])).

tff(c_26,plain,(
    ! [A_20] : ~ v1_subset_1('#skF_3'(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_636,plain,(
    ! [B_83,A_84] :
      ( ~ v1_xboole_0(B_83)
      | v1_subset_1(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_651,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0('#skF_3'(A_20))
      | v1_subset_1('#skF_3'(A_20),A_20)
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_28,c_636])).

tff(c_660,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0('#skF_3'(A_20))
      | v1_xboole_0(A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_651])).

tff(c_4430,plain,(
    ! [A_162] :
      ( '#skF_3'(A_162) = A_162
      | ~ v1_zfmisc_1(A_162)
      | v1_xboole_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_4360,c_660])).

tff(c_4433,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_4430])).

tff(c_4436,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4433])).

tff(c_4571,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4436,c_26])).

tff(c_4631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_4571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  
% 4.92/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 4.92/1.94  
% 4.92/1.94  %Foreground sorts:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Background operators:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Foreground operators:
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.94  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.92/1.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.92/1.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.92/1.94  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.92/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.92/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.92/1.94  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.92/1.94  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.92/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.92/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.94  
% 4.92/1.96  tff(f_55, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.92/1.96  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 4.92/1.96  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.92/1.96  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.92/1.96  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.92/1.96  tff(f_104, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.92/1.96  tff(f_73, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.92/1.96  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 4.92/1.96  tff(c_22, plain, (![A_16]: (~v1_xboole_0(k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.92/1.96  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.92/1.96  tff(c_40, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.92/1.96  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.92/1.96  tff(c_248, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.92/1.96  tff(c_257, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_248])).
% 4.92/1.96  tff(c_262, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_257])).
% 4.92/1.96  tff(c_576, plain, (![A_81, B_82]: (m1_subset_1(k6_domain_1(A_81, B_82), k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.92/1.96  tff(c_585, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_262, c_576])).
% 4.92/1.96  tff(c_589, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_585])).
% 4.92/1.96  tff(c_590, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_589])).
% 4.92/1.96  tff(c_30, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.92/1.96  tff(c_598, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_590, c_30])).
% 4.92/1.96  tff(c_38, plain, (![B_30, A_28]: (B_30=A_28 | ~r1_tarski(A_28, B_30) | ~v1_zfmisc_1(B_30) | v1_xboole_0(B_30) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.92/1.96  tff(c_601, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_598, c_38])).
% 4.92/1.96  tff(c_611, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_601])).
% 4.92/1.96  tff(c_612, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22, c_46, c_611])).
% 4.92/1.96  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.92/1.96  tff(c_263, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_42])).
% 4.92/1.96  tff(c_618, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_263])).
% 4.92/1.96  tff(c_28, plain, (![A_20]: (m1_subset_1('#skF_3'(A_20), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.92/1.96  tff(c_68, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.92/1.96  tff(c_76, plain, (![A_20]: (r1_tarski('#skF_3'(A_20), A_20))), inference(resolution, [status(thm)], [c_28, c_68])).
% 4.92/1.96  tff(c_448, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(A_77, B_76) | ~v1_zfmisc_1(B_76) | v1_xboole_0(B_76) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.92/1.96  tff(c_4360, plain, (![A_160]: ('#skF_3'(A_160)=A_160 | ~v1_zfmisc_1(A_160) | v1_xboole_0(A_160) | v1_xboole_0('#skF_3'(A_160)))), inference(resolution, [status(thm)], [c_76, c_448])).
% 4.92/1.96  tff(c_26, plain, (![A_20]: (~v1_subset_1('#skF_3'(A_20), A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.92/1.96  tff(c_636, plain, (![B_83, A_84]: (~v1_xboole_0(B_83) | v1_subset_1(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.92/1.96  tff(c_651, plain, (![A_20]: (~v1_xboole_0('#skF_3'(A_20)) | v1_subset_1('#skF_3'(A_20), A_20) | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_28, c_636])).
% 4.92/1.96  tff(c_660, plain, (![A_20]: (~v1_xboole_0('#skF_3'(A_20)) | v1_xboole_0(A_20))), inference(negUnitSimplification, [status(thm)], [c_26, c_651])).
% 4.92/1.96  tff(c_4430, plain, (![A_162]: ('#skF_3'(A_162)=A_162 | ~v1_zfmisc_1(A_162) | v1_xboole_0(A_162))), inference(resolution, [status(thm)], [c_4360, c_660])).
% 4.92/1.96  tff(c_4433, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_4430])).
% 4.92/1.96  tff(c_4436, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_4433])).
% 4.92/1.96  tff(c_4571, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4436, c_26])).
% 4.92/1.96  tff(c_4631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_618, c_4571])).
% 4.92/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.96  
% 4.92/1.96  Inference rules
% 4.92/1.96  ----------------------
% 4.92/1.96  #Ref     : 0
% 4.92/1.96  #Sup     : 1201
% 4.92/1.96  #Fact    : 0
% 4.92/1.96  #Define  : 0
% 4.92/1.96  #Split   : 2
% 4.92/1.96  #Chain   : 0
% 4.92/1.96  #Close   : 0
% 4.92/1.96  
% 4.92/1.96  Ordering : KBO
% 4.92/1.96  
% 4.92/1.96  Simplification rules
% 4.92/1.96  ----------------------
% 4.92/1.96  #Subsume      : 491
% 4.92/1.96  #Demod        : 718
% 4.92/1.96  #Tautology    : 386
% 4.92/1.96  #SimpNegUnit  : 20
% 4.92/1.96  #BackRed      : 8
% 4.92/1.96  
% 4.92/1.96  #Partial instantiations: 0
% 4.92/1.96  #Strategies tried      : 1
% 4.92/1.96  
% 4.92/1.96  Timing (in seconds)
% 4.92/1.96  ----------------------
% 4.92/1.96  Preprocessing        : 0.34
% 4.92/1.96  Parsing              : 0.18
% 4.92/1.96  CNF conversion       : 0.02
% 4.92/1.96  Main loop            : 0.79
% 4.92/1.96  Inferencing          : 0.25
% 4.92/1.96  Reduction            : 0.25
% 4.92/1.96  Demodulation         : 0.18
% 4.92/1.96  BG Simplification    : 0.03
% 4.92/1.96  Subsumption          : 0.19
% 4.92/1.96  Abstraction          : 0.04
% 4.92/1.96  MUC search           : 0.00
% 4.92/1.96  Cooper               : 0.00
% 4.92/1.96  Total                : 1.16
% 4.92/1.96  Index Insertion      : 0.00
% 4.92/1.96  Index Deletion       : 0.00
% 4.92/1.96  Index Matching       : 0.00
% 4.92/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
