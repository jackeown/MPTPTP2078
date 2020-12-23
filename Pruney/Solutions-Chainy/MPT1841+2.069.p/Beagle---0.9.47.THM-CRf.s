%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :    9 (  13 expanded)
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

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [A_33,B_34] :
      ( k6_domain_1(A_33,B_34) = k1_tarski(B_34)
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_68,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_65])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_32])).

tff(c_75,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k6_domain_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_75])).

tff(c_88,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_84])).

tff(c_89,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_88])).

tff(c_302,plain,(
    ! [B_60,A_61] :
      ( ~ v1_subset_1(B_60,A_61)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_308,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_302])).

tff(c_317,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_69,c_308])).

tff(c_318,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_317])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_323,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_49,plain,(
    ! [B_26,A_27] :
      ( ~ r1_tarski(B_26,A_27)
      | ~ r2_hidden(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [C_7] : ~ r1_tarski(k1_tarski(C_7),C_7) ),
    inference(resolution,[status(thm)],[c_8,c_49])).

tff(c_333,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_53])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:08:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.28  
% 2.27/1.29  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.29  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.27/1.29  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.29  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.27/1.29  tff(f_81, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.27/1.29  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.29  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.27/1.29  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.27/1.29  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.29  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.27/1.29  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.27/1.29  tff(c_34, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.27/1.29  tff(c_62, plain, (![A_33, B_34]: (k6_domain_1(A_33, B_34)=k1_tarski(B_34) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.29  tff(c_65, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.27/1.29  tff(c_68, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_65])).
% 2.27/1.29  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.27/1.29  tff(c_69, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_32])).
% 2.27/1.29  tff(c_75, plain, (![A_37, B_38]: (m1_subset_1(k6_domain_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.29  tff(c_84, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_75])).
% 2.27/1.29  tff(c_88, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_84])).
% 2.27/1.29  tff(c_89, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_88])).
% 2.27/1.29  tff(c_302, plain, (![B_60, A_61]: (~v1_subset_1(B_60, A_61) | v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.27/1.29  tff(c_308, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_89, c_302])).
% 2.27/1.29  tff(c_317, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_69, c_308])).
% 2.27/1.29  tff(c_318, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_317])).
% 2.27/1.29  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.29  tff(c_323, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_318, c_2])).
% 2.27/1.29  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.29  tff(c_49, plain, (![B_26, A_27]: (~r1_tarski(B_26, A_27) | ~r2_hidden(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.29  tff(c_53, plain, (![C_7]: (~r1_tarski(k1_tarski(C_7), C_7))), inference(resolution, [status(thm)], [c_8, c_49])).
% 2.27/1.29  tff(c_333, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_323, c_53])).
% 2.27/1.29  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_333])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 64
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 1
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 3
% 2.27/1.29  #Demod        : 36
% 2.27/1.29  #Tautology    : 27
% 2.27/1.29  #SimpNegUnit  : 7
% 2.27/1.29  #BackRed      : 13
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.29  Preprocessing        : 0.29
% 2.27/1.29  Parsing              : 0.15
% 2.27/1.29  CNF conversion       : 0.02
% 2.27/1.29  Main loop            : 0.22
% 2.27/1.29  Inferencing          : 0.08
% 2.27/1.29  Reduction            : 0.07
% 2.27/1.29  Demodulation         : 0.04
% 2.27/1.29  BG Simplification    : 0.02
% 2.27/1.29  Subsumption          : 0.04
% 2.27/1.29  Abstraction          : 0.02
% 2.27/1.29  MUC search           : 0.00
% 2.27/1.29  Cooper               : 0.00
% 2.27/1.30  Total                : 0.54
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
