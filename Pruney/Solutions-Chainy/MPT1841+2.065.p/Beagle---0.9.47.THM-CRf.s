%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:36 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_86,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_73,plain,(
    ! [A_36,B_37] :
      ( k6_domain_1(A_36,B_37) = k1_tarski(B_37)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_79,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_76])).

tff(c_34,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_81,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_34])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k6_domain_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_86])).

tff(c_99,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_95])).

tff(c_100,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_99])).

tff(c_380,plain,(
    ! [B_67,A_68] :
      ( ~ v1_subset_1(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_386,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_380])).

tff(c_395,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_81,c_386])).

tff(c_396,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_395])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_55,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_403,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_396,c_58])).

tff(c_10,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [B_26,A_27] :
      ( ~ r1_tarski(B_26,A_27)
      | ~ r2_hidden(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [C_8] : ~ r1_tarski(k1_tarski(C_8),C_8) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_418,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_54])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.30  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.27/1.30  
% 2.27/1.30  %Foreground sorts:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Background operators:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Foreground operators:
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.30  
% 2.27/1.31  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.31  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.27/1.31  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.31  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.27/1.31  tff(f_86, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.27/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.27/1.31  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.27/1.31  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.27/1.31  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.27/1.31  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.27/1.31  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_32, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_36, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_73, plain, (![A_36, B_37]: (k6_domain_1(A_36, B_37)=k1_tarski(B_37) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.31  tff(c_76, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_73])).
% 2.27/1.31  tff(c_79, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_76])).
% 2.27/1.31  tff(c_34, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.27/1.31  tff(c_81, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_34])).
% 2.27/1.31  tff(c_86, plain, (![A_40, B_41]: (m1_subset_1(k6_domain_1(A_40, B_41), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.27/1.31  tff(c_95, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_86])).
% 2.27/1.31  tff(c_99, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_95])).
% 2.27/1.31  tff(c_100, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_99])).
% 2.27/1.31  tff(c_380, plain, (![B_67, A_68]: (~v1_subset_1(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.27/1.31  tff(c_386, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_100, c_380])).
% 2.27/1.31  tff(c_395, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_81, c_386])).
% 2.27/1.31  tff(c_396, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_395])).
% 2.27/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.27/1.31  tff(c_55, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.31  tff(c_58, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.27/1.31  tff(c_403, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_396, c_58])).
% 2.27/1.31  tff(c_10, plain, (![C_8]: (r2_hidden(C_8, k1_tarski(C_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.31  tff(c_50, plain, (![B_26, A_27]: (~r1_tarski(B_26, A_27) | ~r2_hidden(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.31  tff(c_54, plain, (![C_8]: (~r1_tarski(k1_tarski(C_8), C_8))), inference(resolution, [status(thm)], [c_10, c_50])).
% 2.27/1.31  tff(c_418, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_403, c_54])).
% 2.27/1.31  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_418])).
% 2.27/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  Inference rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Ref     : 0
% 2.27/1.31  #Sup     : 83
% 2.27/1.31  #Fact    : 0
% 2.27/1.31  #Define  : 0
% 2.27/1.31  #Split   : 1
% 2.27/1.31  #Chain   : 0
% 2.27/1.31  #Close   : 0
% 2.27/1.31  
% 2.27/1.31  Ordering : KBO
% 2.27/1.31  
% 2.27/1.31  Simplification rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Subsume      : 4
% 2.27/1.31  #Demod        : 46
% 2.27/1.31  #Tautology    : 39
% 2.27/1.31  #SimpNegUnit  : 7
% 2.27/1.31  #BackRed      : 13
% 2.27/1.31  
% 2.27/1.31  #Partial instantiations: 0
% 2.27/1.31  #Strategies tried      : 1
% 2.27/1.31  
% 2.27/1.31  Timing (in seconds)
% 2.27/1.31  ----------------------
% 2.27/1.31  Preprocessing        : 0.30
% 2.27/1.31  Parsing              : 0.16
% 2.27/1.31  CNF conversion       : 0.02
% 2.27/1.31  Main loop            : 0.24
% 2.27/1.31  Inferencing          : 0.09
% 2.27/1.31  Reduction            : 0.07
% 2.27/1.31  Demodulation         : 0.05
% 2.27/1.31  BG Simplification    : 0.02
% 2.27/1.31  Subsumption          : 0.05
% 2.27/1.31  Abstraction          : 0.02
% 2.27/1.31  MUC search           : 0.00
% 2.27/1.31  Cooper               : 0.00
% 2.27/1.31  Total                : 0.57
% 2.27/1.31  Index Insertion      : 0.00
% 2.27/1.31  Index Deletion       : 0.00
% 2.27/1.31  Index Matching       : 0.00
% 2.27/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
