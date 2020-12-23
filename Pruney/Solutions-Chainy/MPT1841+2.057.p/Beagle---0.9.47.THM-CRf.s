%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [B_41,A_42,A_43] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_hidden(A_42,A_43)
      | ~ r1_tarski(A_43,B_41) ) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_81,plain,(
    ! [B_44,C_45] :
      ( ~ v1_xboole_0(B_44)
      | ~ r1_tarski(k1_tarski(C_45),B_44) ) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_86,plain,(
    ! [C_45] : ~ v1_xboole_0(k1_tarski(C_45)) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_87,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_97,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_93])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_99,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_36])).

tff(c_108,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_108])).

tff(c_128,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_129,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_128])).

tff(c_222,plain,(
    ! [B_67,A_68] :
      ( ~ v1_subset_1(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_225,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_222])).

tff(c_234,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_99,c_225])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_86,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.12/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.25  
% 2.12/1.26  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.12/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.26  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.12/1.26  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.12/1.26  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.12/1.26  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.12/1.26  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.12/1.26  tff(f_85, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.12/1.26  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.26  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.26  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.26  tff(c_73, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.26  tff(c_77, plain, (![B_41, A_42, A_43]: (~v1_xboole_0(B_41) | ~r2_hidden(A_42, A_43) | ~r1_tarski(A_43, B_41))), inference(resolution, [status(thm)], [c_24, c_73])).
% 2.12/1.26  tff(c_81, plain, (![B_44, C_45]: (~v1_xboole_0(B_44) | ~r1_tarski(k1_tarski(C_45), B_44))), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.12/1.26  tff(c_86, plain, (![C_45]: (~v1_xboole_0(k1_tarski(C_45)))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.12/1.26  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.26  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.26  tff(c_87, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.12/1.26  tff(c_93, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.12/1.26  tff(c_97, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_93])).
% 2.12/1.26  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.12/1.26  tff(c_99, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_36])).
% 2.12/1.26  tff(c_108, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.26  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_108])).
% 2.12/1.26  tff(c_128, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_122])).
% 2.12/1.26  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_128])).
% 2.12/1.26  tff(c_222, plain, (![B_67, A_68]: (~v1_subset_1(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.26  tff(c_225, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_222])).
% 2.12/1.26  tff(c_234, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_99, c_225])).
% 2.12/1.26  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_86, c_234])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 43
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 2
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 6
% 2.12/1.26  #Demod        : 9
% 2.12/1.26  #Tautology    : 14
% 2.12/1.26  #SimpNegUnit  : 4
% 2.12/1.26  #BackRed      : 1
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.31
% 2.12/1.26  Parsing              : 0.16
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.19
% 2.12/1.26  Inferencing          : 0.07
% 2.12/1.26  Reduction            : 0.05
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.26  BG Simplification    : 0.02
% 2.12/1.27  Subsumption          : 0.04
% 2.12/1.27  Abstraction          : 0.01
% 2.12/1.27  MUC search           : 0.00
% 2.12/1.27  Cooper               : 0.00
% 2.12/1.27  Total                : 0.52
% 2.12/1.27  Index Insertion      : 0.00
% 2.12/1.27  Index Deletion       : 0.00
% 2.12/1.27  Index Matching       : 0.00
% 2.12/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
