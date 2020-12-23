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
% DateTime   : Thu Dec  3 10:28:29 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 123 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_138,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_141,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_138])).

tff(c_144,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_141])).

tff(c_54,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_145,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_171,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k6_domain_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_180,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_171])).

tff(c_184,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_180])).

tff(c_185,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_184])).

tff(c_299,plain,(
    ! [B_100,A_101] :
      ( ~ v1_subset_1(B_100,A_101)
      | v1_xboole_0(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101))
      | ~ v1_zfmisc_1(A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_302,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_299])).

tff(c_308,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_145,c_302])).

tff(c_309,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_308])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_314,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [A_71,B_72,C_73] : k2_enumset1(A_71,A_71,B_72,C_73) = k1_enumset1(A_71,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [F_16,A_9,C_11,D_12] : r2_hidden(F_16,k2_enumset1(A_9,F_16,C_11,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    ! [A_76,B_77,C_78] : r2_hidden(A_76,k1_enumset1(A_76,B_77,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_18])).

tff(c_158,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_166,plain,(
    ! [A_81] : r2_hidden(A_81,k1_tarski(A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_44,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170,plain,(
    ! [A_81] : ~ r1_tarski(k1_tarski(A_81),A_81) ),
    inference(resolution,[status(thm)],[c_166,c_44])).

tff(c_322,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_170])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:42:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  
% 2.47/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.43  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.43  
% 2.47/1.43  %Foreground sorts:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Background operators:
% 2.47/1.43  
% 2.47/1.43  
% 2.47/1.43  %Foreground operators:
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.47/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.47/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.47/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.43  
% 2.47/1.45  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.47/1.45  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.47/1.45  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.47/1.45  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.47/1.45  tff(f_95, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.47/1.45  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.47/1.45  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.45  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.45  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.47/1.45  tff(f_55, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.47/1.45  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.47/1.45  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.45  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.47/1.45  tff(c_52, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.47/1.45  tff(c_56, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.47/1.45  tff(c_138, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.47/1.45  tff(c_141, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_138])).
% 2.47/1.45  tff(c_144, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_141])).
% 2.47/1.45  tff(c_54, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.47/1.45  tff(c_145, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_54])).
% 2.47/1.45  tff(c_171, plain, (![A_82, B_83]: (m1_subset_1(k6_domain_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.45  tff(c_180, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_171])).
% 2.47/1.45  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_180])).
% 2.47/1.45  tff(c_185, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_184])).
% 2.47/1.45  tff(c_299, plain, (![B_100, A_101]: (~v1_subset_1(B_100, A_101) | v1_xboole_0(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)) | ~v1_zfmisc_1(A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.47/1.45  tff(c_302, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_185, c_299])).
% 2.47/1.45  tff(c_308, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_145, c_302])).
% 2.47/1.45  tff(c_309, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_308])).
% 2.47/1.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.45  tff(c_314, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_309, c_2])).
% 2.47/1.45  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.45  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.45  tff(c_105, plain, (![A_71, B_72, C_73]: (k2_enumset1(A_71, A_71, B_72, C_73)=k1_enumset1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.45  tff(c_18, plain, (![F_16, A_9, C_11, D_12]: (r2_hidden(F_16, k2_enumset1(A_9, F_16, C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.45  tff(c_150, plain, (![A_76, B_77, C_78]: (r2_hidden(A_76, k1_enumset1(A_76, B_77, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_18])).
% 2.47/1.45  tff(c_158, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_150])).
% 2.47/1.45  tff(c_166, plain, (![A_81]: (r2_hidden(A_81, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_158])).
% 2.47/1.45  tff(c_44, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.45  tff(c_170, plain, (![A_81]: (~r1_tarski(k1_tarski(A_81), A_81))), inference(resolution, [status(thm)], [c_166, c_44])).
% 2.47/1.45  tff(c_322, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_314, c_170])).
% 2.47/1.45  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_322])).
% 2.47/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.45  
% 2.47/1.45  Inference rules
% 2.47/1.45  ----------------------
% 2.47/1.45  #Ref     : 0
% 2.47/1.45  #Sup     : 61
% 2.47/1.45  #Fact    : 0
% 2.47/1.45  #Define  : 0
% 2.47/1.45  #Split   : 1
% 2.47/1.45  #Chain   : 0
% 2.47/1.45  #Close   : 0
% 2.47/1.45  
% 2.47/1.45  Ordering : KBO
% 2.47/1.45  
% 2.47/1.45  Simplification rules
% 2.47/1.45  ----------------------
% 2.47/1.45  #Subsume      : 4
% 2.47/1.45  #Demod        : 23
% 2.47/1.45  #Tautology    : 19
% 2.47/1.45  #SimpNegUnit  : 5
% 2.47/1.45  #BackRed      : 11
% 2.47/1.45  
% 2.47/1.45  #Partial instantiations: 0
% 2.47/1.45  #Strategies tried      : 1
% 2.47/1.45  
% 2.47/1.45  Timing (in seconds)
% 2.47/1.45  ----------------------
% 2.47/1.45  Preprocessing        : 0.34
% 2.47/1.45  Parsing              : 0.18
% 2.47/1.45  CNF conversion       : 0.02
% 2.47/1.45  Main loop            : 0.27
% 2.47/1.45  Inferencing          : 0.09
% 2.47/1.45  Reduction            : 0.08
% 2.47/1.45  Demodulation         : 0.05
% 2.47/1.45  BG Simplification    : 0.02
% 2.47/1.45  Subsumption          : 0.06
% 2.47/1.45  Abstraction          : 0.02
% 2.47/1.45  MUC search           : 0.00
% 2.47/1.45  Cooper               : 0.00
% 2.47/1.45  Total                : 0.64
% 2.47/1.45  Index Insertion      : 0.00
% 2.47/1.45  Index Deletion       : 0.00
% 2.47/1.45  Index Matching       : 0.00
% 2.47/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
