%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:30 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 126 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

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

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_168,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_177,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_182,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_177])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_183,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_48])).

tff(c_189,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_189])).

tff(c_209,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_210,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_209])).

tff(c_255,plain,(
    ! [B_78,A_79] :
      ( ~ v1_subset_1(B_78,A_79)
      | v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_258,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_255])).

tff(c_270,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_183,c_258])).

tff(c_271,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_270])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_95,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_281,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_98])).

tff(c_55,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_73,plain,(
    ! [B_38,A_39] :
      ( ~ r1_tarski(B_38,A_39)
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_34] : ~ r1_tarski(k1_tarski(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_298,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_84])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:51:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.25  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.21/1.25  
% 2.21/1.25  %Foreground sorts:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Background operators:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Foreground operators:
% 2.21/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.21/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.21/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.21/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.25  
% 2.21/1.26  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.21/1.26  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.26  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.21/1.26  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.21/1.26  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.21/1.26  tff(f_99, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.21/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.26  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.21/1.26  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.26  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.21/1.26  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.21/1.26  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.26  tff(c_99, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.26  tff(c_103, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.21/1.26  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.21/1.26  tff(c_46, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.21/1.26  tff(c_50, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.21/1.26  tff(c_168, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.21/1.26  tff(c_177, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_168])).
% 2.21/1.26  tff(c_182, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_177])).
% 2.21/1.26  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.21/1.26  tff(c_183, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_48])).
% 2.21/1.26  tff(c_189, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.21/1.26  tff(c_203, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_189])).
% 2.21/1.26  tff(c_209, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_203])).
% 2.21/1.26  tff(c_210, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_209])).
% 2.21/1.26  tff(c_255, plain, (![B_78, A_79]: (~v1_subset_1(B_78, A_79) | v1_xboole_0(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.21/1.26  tff(c_258, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_210, c_255])).
% 2.21/1.26  tff(c_270, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_183, c_258])).
% 2.21/1.26  tff(c_271, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_270])).
% 2.21/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.26  tff(c_95, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.26  tff(c_98, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_95])).
% 2.21/1.26  tff(c_281, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_98])).
% 2.21/1.26  tff(c_55, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.26  tff(c_10, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.26  tff(c_61, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 2.21/1.26  tff(c_73, plain, (![B_38, A_39]: (~r1_tarski(B_38, A_39) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.21/1.26  tff(c_84, plain, (![A_34]: (~r1_tarski(k1_tarski(A_34), A_34))), inference(resolution, [status(thm)], [c_61, c_73])).
% 2.21/1.26  tff(c_298, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_281, c_84])).
% 2.21/1.26  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_298])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 56
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 0
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 5
% 2.21/1.26  #Demod        : 19
% 2.21/1.26  #Tautology    : 21
% 2.21/1.26  #SimpNegUnit  : 3
% 2.21/1.26  #BackRed      : 7
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.27  Preprocessing        : 0.32
% 2.21/1.27  Parsing              : 0.17
% 2.21/1.27  CNF conversion       : 0.02
% 2.21/1.27  Main loop            : 0.19
% 2.21/1.27  Inferencing          : 0.07
% 2.21/1.27  Reduction            : 0.06
% 2.21/1.27  Demodulation         : 0.04
% 2.21/1.27  BG Simplification    : 0.02
% 2.21/1.27  Subsumption          : 0.04
% 2.21/1.27  Abstraction          : 0.01
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.54
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
