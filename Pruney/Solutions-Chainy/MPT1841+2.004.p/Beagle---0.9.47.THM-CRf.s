%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:28 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

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
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

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
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_87,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_97,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_93])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_99,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_36])).

tff(c_104,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_104])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_118])).

tff(c_125,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_124])).

tff(c_235,plain,(
    ! [B_69,A_70] :
      ( ~ v1_subset_1(B_69,A_70)
      | v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_238,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_235])).

tff(c_247,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_99,c_238])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_86,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:11:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.28  
% 2.16/1.29  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.29  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.29  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.16/1.29  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.29  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.29  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.16/1.29  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.16/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.29  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.29  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.29  tff(c_73, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.29  tff(c_77, plain, (![B_41, A_42, A_43]: (~v1_xboole_0(B_41) | ~r2_hidden(A_42, A_43) | ~r1_tarski(A_43, B_41))), inference(resolution, [status(thm)], [c_24, c_73])).
% 2.16/1.29  tff(c_81, plain, (![B_44, C_45]: (~v1_xboole_0(B_44) | ~r1_tarski(k1_tarski(C_45), B_44))), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.16/1.29  tff(c_86, plain, (![C_45]: (~v1_xboole_0(k1_tarski(C_45)))), inference(resolution, [status(thm)], [c_6, c_81])).
% 2.16/1.29  tff(c_34, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.16/1.29  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.16/1.29  tff(c_87, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.29  tff(c_93, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.16/1.29  tff(c_97, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_93])).
% 2.16/1.29  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.16/1.29  tff(c_99, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_36])).
% 2.16/1.29  tff(c_104, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.29  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_104])).
% 2.16/1.29  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_118])).
% 2.16/1.29  tff(c_125, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_124])).
% 2.16/1.29  tff(c_235, plain, (![B_69, A_70]: (~v1_subset_1(B_69, A_70) | v1_xboole_0(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.29  tff(c_238, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_235])).
% 2.16/1.29  tff(c_247, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_99, c_238])).
% 2.16/1.29  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_86, c_247])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 46
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 2
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 6
% 2.16/1.29  #Demod        : 8
% 2.16/1.29  #Tautology    : 16
% 2.16/1.29  #SimpNegUnit  : 6
% 2.16/1.29  #BackRed      : 1
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.30  Preprocessing        : 0.30
% 2.16/1.30  Parsing              : 0.16
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.21
% 2.16/1.30  Inferencing          : 0.07
% 2.16/1.30  Reduction            : 0.06
% 2.16/1.30  Demodulation         : 0.04
% 2.16/1.30  BG Simplification    : 0.02
% 2.16/1.30  Subsumption          : 0.05
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.54
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
