%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:38 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   64 (  86 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 142 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_26,plain,(
    ! [A_10] : v1_xboole_0('#skF_3'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(B_35)
      | B_35 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_79,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_86,plain,(
    ! [A_10] : '#skF_3'(A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_28,plain,(
    ! [A_10] : m1_subset_1('#skF_3'(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_119,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_89,c_119])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_169,plain,(
    ! [A_62,B_63] :
      ( k6_domain_1(A_62,B_63) = k1_tarski(B_63)
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_169])).

tff(c_183,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_178])).

tff(c_46,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_184,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_46])).

tff(c_210,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k6_domain_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_225,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_210])).

tff(c_232,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225])).

tff(c_233,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_232])).

tff(c_248,plain,(
    ! [B_68,A_69] :
      ( ~ v1_subset_1(B_68,A_69)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_251,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_248])).

tff(c_263,plain,
    ( v1_xboole_0(k1_tarski('#skF_5'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_184,c_251])).

tff(c_264,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_263])).

tff(c_78,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_274,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_264,c_78])).

tff(c_53,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_100,plain,(
    ! [B_40,A_41] :
      ( ~ r1_tarski(B_40,A_41)
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,(
    ! [A_30] : ~ r1_tarski(k1_tarski(A_30),A_30) ),
    inference(resolution,[status(thm)],[c_59,c_100])).

tff(c_288,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_111])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.23  
% 2.20/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.23  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.33/1.23  
% 2.33/1.23  %Foreground sorts:
% 2.33/1.23  
% 2.33/1.23  
% 2.33/1.23  %Background operators:
% 2.33/1.23  
% 2.33/1.23  
% 2.33/1.23  %Foreground operators:
% 2.33/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.33/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.33/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.33/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.33/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.23  
% 2.39/1.24  tff(f_50, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.39/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.24  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.39/1.24  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.24  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.39/1.24  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.39/1.24  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.39/1.24  tff(f_95, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.39/1.24  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.24  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.39/1.24  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.39/1.24  tff(c_26, plain, (![A_10]: (v1_xboole_0('#skF_3'(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.39/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.39/1.24  tff(c_72, plain, (![B_35, A_36]: (~v1_xboole_0(B_35) | B_35=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.39/1.24  tff(c_79, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.39/1.24  tff(c_86, plain, (![A_10]: ('#skF_3'(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.39/1.24  tff(c_28, plain, (![A_10]: (m1_subset_1('#skF_3'(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.39/1.24  tff(c_89, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_28])).
% 2.39/1.24  tff(c_119, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.24  tff(c_123, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_89, c_119])).
% 2.39/1.24  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.39/1.24  tff(c_44, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.39/1.24  tff(c_48, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.39/1.24  tff(c_169, plain, (![A_62, B_63]: (k6_domain_1(A_62, B_63)=k1_tarski(B_63) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.39/1.24  tff(c_178, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_169])).
% 2.39/1.24  tff(c_183, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_178])).
% 2.39/1.24  tff(c_46, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.39/1.24  tff(c_184, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_46])).
% 2.39/1.24  tff(c_210, plain, (![A_66, B_67]: (m1_subset_1(k6_domain_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.24  tff(c_225, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_210])).
% 2.39/1.24  tff(c_232, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_225])).
% 2.39/1.24  tff(c_233, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_232])).
% 2.39/1.24  tff(c_248, plain, (![B_68, A_69]: (~v1_subset_1(B_68, A_69) | v1_xboole_0(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.39/1.24  tff(c_251, plain, (~v1_subset_1(k1_tarski('#skF_5'), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_233, c_248])).
% 2.39/1.24  tff(c_263, plain, (v1_xboole_0(k1_tarski('#skF_5')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_184, c_251])).
% 2.39/1.24  tff(c_264, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_263])).
% 2.39/1.24  tff(c_78, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.39/1.24  tff(c_274, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_264, c_78])).
% 2.39/1.24  tff(c_53, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.24  tff(c_10, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.24  tff(c_59, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 2.39/1.24  tff(c_100, plain, (![B_40, A_41]: (~r1_tarski(B_40, A_41) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.24  tff(c_111, plain, (![A_30]: (~r1_tarski(k1_tarski(A_30), A_30))), inference(resolution, [status(thm)], [c_59, c_100])).
% 2.39/1.24  tff(c_288, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_274, c_111])).
% 2.39/1.24  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_288])).
% 2.39/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.24  
% 2.39/1.24  Inference rules
% 2.39/1.24  ----------------------
% 2.39/1.24  #Ref     : 0
% 2.39/1.24  #Sup     : 53
% 2.39/1.24  #Fact    : 0
% 2.39/1.24  #Define  : 0
% 2.39/1.25  #Split   : 0
% 2.39/1.25  #Chain   : 0
% 2.39/1.25  #Close   : 0
% 2.39/1.25  
% 2.39/1.25  Ordering : KBO
% 2.39/1.25  
% 2.39/1.25  Simplification rules
% 2.39/1.25  ----------------------
% 2.39/1.25  #Subsume      : 6
% 2.39/1.25  #Demod        : 19
% 2.39/1.25  #Tautology    : 20
% 2.39/1.25  #SimpNegUnit  : 3
% 2.39/1.25  #BackRed      : 7
% 2.39/1.25  
% 2.39/1.25  #Partial instantiations: 0
% 2.39/1.25  #Strategies tried      : 1
% 2.39/1.25  
% 2.39/1.25  Timing (in seconds)
% 2.39/1.25  ----------------------
% 2.39/1.25  Preprocessing        : 0.31
% 2.39/1.25  Parsing              : 0.16
% 2.39/1.25  CNF conversion       : 0.02
% 2.39/1.25  Main loop            : 0.18
% 2.39/1.25  Inferencing          : 0.07
% 2.39/1.25  Reduction            : 0.06
% 2.39/1.25  Demodulation         : 0.04
% 2.39/1.25  BG Simplification    : 0.02
% 2.39/1.25  Subsumption          : 0.03
% 2.39/1.25  Abstraction          : 0.01
% 2.39/1.25  MUC search           : 0.00
% 2.39/1.25  Cooper               : 0.00
% 2.39/1.25  Total                : 0.51
% 2.39/1.25  Index Insertion      : 0.00
% 2.39/1.25  Index Deletion       : 0.00
% 2.39/1.25  Index Matching       : 0.00
% 2.39/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
