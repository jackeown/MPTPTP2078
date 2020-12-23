%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 171 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_93,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_93])).

tff(c_107,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_102])).

tff(c_113,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k6_domain_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_113])).

tff(c_126,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_127,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_126])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_24])).

tff(c_166,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(A_52,B_51)
      | ~ v1_zfmisc_1(B_51)
      | v1_xboole_0(B_51)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_172,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_135,c_166])).

tff(c_179,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_172])).

tff(c_180,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_40,c_179])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_108,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_36])).

tff(c_184,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_108])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1('#skF_4'(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    ! [A_13] : r1_tarski('#skF_4'(A_13),A_13) ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_308,plain,(
    ! [A_61] :
      ( '#skF_4'(A_61) = A_61
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61)
      | v1_xboole_0('#skF_4'(A_61)) ) ),
    inference(resolution,[status(thm)],[c_91,c_166])).

tff(c_20,plain,(
    ! [A_13] : ~ v1_subset_1('#skF_4'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | v1_subset_1(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_156,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_4'(A_13))
      | v1_subset_1('#skF_4'(A_13),A_13)
      | v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_144])).

tff(c_164,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_4'(A_13))
      | v1_xboole_0(A_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_156])).

tff(c_320,plain,(
    ! [A_64] :
      ( '#skF_4'(A_64) = A_64
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_308,c_164])).

tff(c_323,plain,
    ( '#skF_4'('#skF_5') = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_320])).

tff(c_326,plain,(
    '#skF_4'('#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_323])).

tff(c_339,plain,(
    ~ v1_subset_1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_20])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:59:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.26  
% 2.40/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.26  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.40/1.26  
% 2.40/1.26  %Foreground sorts:
% 2.40/1.26  
% 2.40/1.26  
% 2.40/1.26  %Background operators:
% 2.40/1.26  
% 2.40/1.26  
% 2.40/1.26  %Foreground operators:
% 2.40/1.26  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.40/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.40/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.40/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.40/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.40/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.40/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.40/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.26  
% 2.40/1.28  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.40/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.40/1.28  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.40/1.28  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.40/1.28  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.40/1.28  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.28  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.40/1.28  tff(f_56, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.40/1.28  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.40/1.28  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.28  tff(c_43, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.28  tff(c_47, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_43])).
% 2.40/1.28  tff(c_40, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.28  tff(c_34, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.28  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.28  tff(c_93, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.40/1.28  tff(c_102, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_93])).
% 2.40/1.28  tff(c_107, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_102])).
% 2.40/1.28  tff(c_113, plain, (![A_42, B_43]: (m1_subset_1(k6_domain_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.40/1.28  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_107, c_113])).
% 2.40/1.28  tff(c_126, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_122])).
% 2.40/1.28  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_40, c_126])).
% 2.40/1.28  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.40/1.28  tff(c_135, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_127, c_24])).
% 2.40/1.28  tff(c_166, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(A_52, B_51) | ~v1_zfmisc_1(B_51) | v1_xboole_0(B_51) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.40/1.28  tff(c_172, plain, (k1_tarski('#skF_6')='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_135, c_166])).
% 2.40/1.28  tff(c_179, plain, (k1_tarski('#skF_6')='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_172])).
% 2.40/1.28  tff(c_180, plain, (k1_tarski('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_47, c_40, c_179])).
% 2.40/1.28  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.28  tff(c_108, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_36])).
% 2.40/1.28  tff(c_184, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_108])).
% 2.40/1.28  tff(c_22, plain, (![A_13]: (m1_subset_1('#skF_4'(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.28  tff(c_83, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.40/1.28  tff(c_91, plain, (![A_13]: (r1_tarski('#skF_4'(A_13), A_13))), inference(resolution, [status(thm)], [c_22, c_83])).
% 2.40/1.28  tff(c_308, plain, (![A_61]: ('#skF_4'(A_61)=A_61 | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61) | v1_xboole_0('#skF_4'(A_61)))), inference(resolution, [status(thm)], [c_91, c_166])).
% 2.40/1.28  tff(c_20, plain, (![A_13]: (~v1_subset_1('#skF_4'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.28  tff(c_144, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | v1_subset_1(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.40/1.28  tff(c_156, plain, (![A_13]: (~v1_xboole_0('#skF_4'(A_13)) | v1_subset_1('#skF_4'(A_13), A_13) | v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_22, c_144])).
% 2.40/1.28  tff(c_164, plain, (![A_13]: (~v1_xboole_0('#skF_4'(A_13)) | v1_xboole_0(A_13))), inference(negUnitSimplification, [status(thm)], [c_20, c_156])).
% 2.40/1.28  tff(c_320, plain, (![A_64]: ('#skF_4'(A_64)=A_64 | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_308, c_164])).
% 2.40/1.28  tff(c_323, plain, ('#skF_4'('#skF_5')='#skF_5' | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_320])).
% 2.40/1.28  tff(c_326, plain, ('#skF_4'('#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_40, c_323])).
% 2.40/1.28  tff(c_339, plain, (~v1_subset_1('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_326, c_20])).
% 2.40/1.28  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_339])).
% 2.40/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.28  
% 2.40/1.28  Inference rules
% 2.40/1.28  ----------------------
% 2.40/1.28  #Ref     : 0
% 2.40/1.28  #Sup     : 64
% 2.40/1.28  #Fact    : 0
% 2.40/1.28  #Define  : 0
% 2.40/1.28  #Split   : 2
% 2.40/1.28  #Chain   : 0
% 2.40/1.28  #Close   : 0
% 2.40/1.28  
% 2.40/1.28  Ordering : KBO
% 2.40/1.28  
% 2.40/1.28  Simplification rules
% 2.40/1.28  ----------------------
% 2.40/1.28  #Subsume      : 7
% 2.40/1.28  #Demod        : 27
% 2.40/1.28  #Tautology    : 28
% 2.40/1.28  #SimpNegUnit  : 16
% 2.40/1.28  #BackRed      : 5
% 2.40/1.28  
% 2.40/1.28  #Partial instantiations: 0
% 2.40/1.28  #Strategies tried      : 1
% 2.40/1.28  
% 2.40/1.28  Timing (in seconds)
% 2.40/1.28  ----------------------
% 2.40/1.28  Preprocessing        : 0.31
% 2.40/1.28  Parsing              : 0.17
% 2.40/1.28  CNF conversion       : 0.02
% 2.40/1.28  Main loop            : 0.21
% 2.40/1.28  Inferencing          : 0.08
% 2.40/1.28  Reduction            : 0.06
% 2.40/1.28  Demodulation         : 0.04
% 2.40/1.28  BG Simplification    : 0.02
% 2.40/1.28  Subsumption          : 0.03
% 2.40/1.28  Abstraction          : 0.01
% 2.40/1.28  MUC search           : 0.00
% 2.40/1.28  Cooper               : 0.00
% 2.40/1.28  Total                : 0.55
% 2.40/1.28  Index Insertion      : 0.00
% 2.40/1.28  Index Deletion       : 0.00
% 2.40/1.28  Index Matching       : 0.00
% 2.40/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
