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
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   60 (  98 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 189 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_32])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_406,plain,(
    ! [A_95,A_96] :
      ( r1_tarski(A_95,k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96)))
      | ~ r1_tarski(A_95,A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    ! [A_10,A_45,B_46] :
      ( v4_relat_1(A_10,A_45)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_434,plain,(
    ! [A_95,A_96] :
      ( v4_relat_1(A_95,k1_relat_1(A_96))
      | ~ r1_tarski(A_95,A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_406,c_126])).

tff(c_127,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_624,plain,(
    ! [A_134,A_135,B_136] :
      ( r1_tarski(A_134,A_135)
      | ~ r1_tarski(A_134,k1_relat_1(B_136))
      | ~ v4_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_20,c_171])).

tff(c_1721,plain,(
    ! [B_258,A_259,B_260] :
      ( r1_tarski(k1_relat_1(B_258),A_259)
      | ~ v4_relat_1(B_260,A_259)
      | ~ v1_relat_1(B_260)
      | ~ v4_relat_1(B_258,k1_relat_1(B_260))
      | ~ v1_relat_1(B_258) ) ),
    inference(resolution,[status(thm)],[c_20,c_624])).

tff(c_1763,plain,(
    ! [B_258] :
      ( r1_tarski(k1_relat_1(B_258),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1(B_258,k1_relat_1('#skF_4'))
      | ~ v1_relat_1(B_258) ) ),
    inference(resolution,[status(thm)],[c_127,c_1721])).

tff(c_1836,plain,(
    ! [B_263] :
      ( r1_tarski(k1_relat_1(B_263),'#skF_3')
      | ~ v4_relat_1(B_263,k1_relat_1('#skF_4'))
      | ~ v1_relat_1(B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1763])).

tff(c_1868,plain,(
    ! [A_95] :
      ( r1_tarski(k1_relat_1(A_95),'#skF_3')
      | ~ v1_relat_1(A_95)
      | ~ r1_tarski(A_95,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_434,c_1836])).

tff(c_1896,plain,(
    ! [A_95] :
      ( r1_tarski(k1_relat_1(A_95),'#skF_3')
      | ~ v1_relat_1(A_95)
      | ~ r1_tarski(A_95,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1868])).

tff(c_34,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_247,plain,(
    ! [A_68,C_69,B_70,D_71] :
      ( r1_tarski(k2_zfmisc_1(A_68,C_69),k2_zfmisc_1(B_70,D_71))
      | ~ r1_tarski(C_69,D_71)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_973,plain,(
    ! [B_180,D_181,A_182,C_183,A_184] :
      ( r1_tarski(A_182,k2_zfmisc_1(B_180,D_181))
      | ~ r1_tarski(A_182,k2_zfmisc_1(A_184,C_183))
      | ~ r1_tarski(C_183,D_181)
      | ~ r1_tarski(A_184,B_180) ) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_2560,plain,(
    ! [A_306,B_307,D_308] :
      ( r1_tarski(A_306,k2_zfmisc_1(B_307,D_308))
      | ~ r1_tarski(k2_relat_1(A_306),D_308)
      | ~ r1_tarski(k1_relat_1(A_306),B_307)
      | ~ v1_relat_1(A_306) ) ),
    inference(resolution,[status(thm)],[c_24,c_973])).

tff(c_2574,plain,(
    ! [B_307] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_307,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_307)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_2560])).

tff(c_2586,plain,(
    ! [B_309] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_309,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2574])).

tff(c_2590,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1896,c_2586])).

tff(c_2624,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_64,c_2590])).

tff(c_2626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.78  
% 4.50/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.78  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.50/1.78  
% 4.50/1.78  %Foreground sorts:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Background operators:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Foreground operators:
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.50/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.50/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.50/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.50/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.50/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.78  
% 4.58/1.79  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.58/1.79  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 4.58/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.58/1.79  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.58/1.79  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.58/1.79  tff(f_66, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.58/1.79  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.58/1.79  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.58/1.79  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.58/1.79  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 4.58/1.79  tff(c_40, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.79  tff(c_32, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.79  tff(c_44, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_32])).
% 4.58/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.79  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.58/1.79  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.79  tff(c_54, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.58/1.79  tff(c_60, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_54])).
% 4.58/1.79  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 4.58/1.79  tff(c_24, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.58/1.79  tff(c_171, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.79  tff(c_406, plain, (![A_95, A_96]: (r1_tarski(A_95, k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96))) | ~r1_tarski(A_95, A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_24, c_171])).
% 4.58/1.79  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.79  tff(c_118, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.58/1.79  tff(c_126, plain, (![A_10, A_45, B_46]: (v4_relat_1(A_10, A_45) | ~r1_tarski(A_10, k2_zfmisc_1(A_45, B_46)))), inference(resolution, [status(thm)], [c_14, c_118])).
% 4.58/1.79  tff(c_434, plain, (![A_95, A_96]: (v4_relat_1(A_95, k1_relat_1(A_96)) | ~r1_tarski(A_95, A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_406, c_126])).
% 4.58/1.79  tff(c_127, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_118])).
% 4.58/1.79  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.58/1.79  tff(c_624, plain, (![A_134, A_135, B_136]: (r1_tarski(A_134, A_135) | ~r1_tarski(A_134, k1_relat_1(B_136)) | ~v4_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_20, c_171])).
% 4.58/1.79  tff(c_1721, plain, (![B_258, A_259, B_260]: (r1_tarski(k1_relat_1(B_258), A_259) | ~v4_relat_1(B_260, A_259) | ~v1_relat_1(B_260) | ~v4_relat_1(B_258, k1_relat_1(B_260)) | ~v1_relat_1(B_258))), inference(resolution, [status(thm)], [c_20, c_624])).
% 4.58/1.79  tff(c_1763, plain, (![B_258]: (r1_tarski(k1_relat_1(B_258), '#skF_3') | ~v1_relat_1('#skF_4') | ~v4_relat_1(B_258, k1_relat_1('#skF_4')) | ~v1_relat_1(B_258))), inference(resolution, [status(thm)], [c_127, c_1721])).
% 4.58/1.79  tff(c_1836, plain, (![B_263]: (r1_tarski(k1_relat_1(B_263), '#skF_3') | ~v4_relat_1(B_263, k1_relat_1('#skF_4')) | ~v1_relat_1(B_263))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1763])).
% 4.58/1.79  tff(c_1868, plain, (![A_95]: (r1_tarski(k1_relat_1(A_95), '#skF_3') | ~v1_relat_1(A_95) | ~r1_tarski(A_95, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_434, c_1836])).
% 4.58/1.79  tff(c_1896, plain, (![A_95]: (r1_tarski(k1_relat_1(A_95), '#skF_3') | ~v1_relat_1(A_95) | ~r1_tarski(A_95, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1868])).
% 4.58/1.79  tff(c_34, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.79  tff(c_247, plain, (![A_68, C_69, B_70, D_71]: (r1_tarski(k2_zfmisc_1(A_68, C_69), k2_zfmisc_1(B_70, D_71)) | ~r1_tarski(C_69, D_71) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.79  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.79  tff(c_973, plain, (![B_180, D_181, A_182, C_183, A_184]: (r1_tarski(A_182, k2_zfmisc_1(B_180, D_181)) | ~r1_tarski(A_182, k2_zfmisc_1(A_184, C_183)) | ~r1_tarski(C_183, D_181) | ~r1_tarski(A_184, B_180))), inference(resolution, [status(thm)], [c_247, c_8])).
% 4.58/1.79  tff(c_2560, plain, (![A_306, B_307, D_308]: (r1_tarski(A_306, k2_zfmisc_1(B_307, D_308)) | ~r1_tarski(k2_relat_1(A_306), D_308) | ~r1_tarski(k1_relat_1(A_306), B_307) | ~v1_relat_1(A_306))), inference(resolution, [status(thm)], [c_24, c_973])).
% 4.58/1.79  tff(c_2574, plain, (![B_307]: (r1_tarski('#skF_4', k2_zfmisc_1(B_307, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_307) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2560])).
% 4.58/1.79  tff(c_2586, plain, (![B_309]: (r1_tarski('#skF_4', k2_zfmisc_1(B_309, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_309))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2574])).
% 4.58/1.79  tff(c_2590, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1896, c_2586])).
% 4.58/1.79  tff(c_2624, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_64, c_2590])).
% 4.58/1.79  tff(c_2626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2624])).
% 4.58/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.79  
% 4.58/1.79  Inference rules
% 4.58/1.79  ----------------------
% 4.58/1.79  #Ref     : 0
% 4.58/1.79  #Sup     : 564
% 4.58/1.79  #Fact    : 0
% 4.58/1.79  #Define  : 0
% 4.58/1.79  #Split   : 15
% 4.58/1.79  #Chain   : 0
% 4.58/1.79  #Close   : 0
% 4.58/1.79  
% 4.58/1.79  Ordering : KBO
% 4.58/1.79  
% 4.58/1.79  Simplification rules
% 4.58/1.79  ----------------------
% 4.58/1.79  #Subsume      : 203
% 4.58/1.79  #Demod        : 185
% 4.58/1.79  #Tautology    : 52
% 4.58/1.79  #SimpNegUnit  : 1
% 4.58/1.79  #BackRed      : 0
% 4.58/1.79  
% 4.58/1.79  #Partial instantiations: 0
% 4.58/1.79  #Strategies tried      : 1
% 4.58/1.79  
% 4.58/1.79  Timing (in seconds)
% 4.58/1.79  ----------------------
% 4.58/1.80  Preprocessing        : 0.29
% 4.58/1.80  Parsing              : 0.17
% 4.58/1.80  CNF conversion       : 0.02
% 4.58/1.80  Main loop            : 0.75
% 4.58/1.80  Inferencing          : 0.25
% 4.58/1.80  Reduction            : 0.23
% 4.58/1.80  Demodulation         : 0.15
% 4.58/1.80  BG Simplification    : 0.02
% 4.58/1.80  Subsumption          : 0.19
% 4.58/1.80  Abstraction          : 0.03
% 4.58/1.80  MUC search           : 0.00
% 4.58/1.80  Cooper               : 0.00
% 4.58/1.80  Total                : 1.07
% 4.58/1.80  Index Insertion      : 0.00
% 4.58/1.80  Index Deletion       : 0.00
% 4.58/1.80  Index Matching       : 0.00
% 4.58/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
