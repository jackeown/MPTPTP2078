%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 170 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 291 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_71,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_relset_1(A_49,B_50,C_51) = k2_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,(
    ! [A_59,B_60,A_61] :
      ( k2_relset_1(A_59,B_60,A_61) = k2_relat_1(A_61)
      | ~ r1_tarski(A_61,k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_154,plain,(
    ! [A_62] :
      ( k2_relset_1('#skF_1','#skF_3',A_62) = k2_relat_1(A_62)
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_132])).

tff(c_162,plain,(
    ! [A_13] :
      ( k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_13)) = k2_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_166,plain,(
    ! [A_13] : k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_13)) = k2_relat_1(k7_relat_1('#skF_4',A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_162])).

tff(c_176,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k2_relset_1(A_64,B_65,C_66),k1_zfmisc_1(B_65))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_310,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(k2_relset_1(A_81,B_82,C_83),B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_350,plain,(
    ! [A_87,B_88,A_89] :
      ( r1_tarski(k2_relset_1(A_87,B_88,A_89),B_88)
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_6,c_310])).

tff(c_929,plain,(
    ! [A_148] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_148)),'#skF_3')
      | ~ r1_tarski(k7_relat_1('#skF_4',A_148),k2_zfmisc_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_350])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_47,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_86,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_47])).

tff(c_91,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_99,plain,(
    ! [A_13] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_103,plain,(
    ! [A_13] : v1_relat_1(k7_relat_1('#skF_4',A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_99])).

tff(c_323,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ r1_tarski(k2_relat_1(C_84),B_86)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_243,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k5_relset_1(A_70,B_71,C_72,D_73) = k7_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_254,plain,(
    ! [D_73] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_73) = k7_relat_1('#skF_4',D_73) ),
    inference(resolution,[status(thm)],[c_26,c_243])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_256,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_24])).

tff(c_328,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_323,c_256])).

tff(c_343,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_328])).

tff(c_418,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_421,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_421])).

tff(c_426,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_945,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_929,c_426])).

tff(c_977,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_945])).

tff(c_980,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_977])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.97/1.45  
% 2.97/1.45  %Foreground sorts:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Background operators:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Foreground operators:
% 2.97/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.97/1.45  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.97/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.45  
% 3.30/1.47  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.30/1.47  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 3.30/1.47  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.30/1.47  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.30/1.47  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.30/1.47  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.30/1.47  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.30/1.47  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.30/1.47  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.30/1.47  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.30/1.47  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.30/1.47  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.47  tff(c_40, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.30/1.47  tff(c_46, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_40])).
% 3.30/1.47  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_46])).
% 3.30/1.47  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.30/1.47  tff(c_30, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.47  tff(c_38, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_30])).
% 3.30/1.47  tff(c_71, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.47  tff(c_78, plain, (![A_44]: (r1_tarski(A_44, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_44, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_71])).
% 3.30/1.47  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.47  tff(c_104, plain, (![A_49, B_50, C_51]: (k2_relset_1(A_49, B_50, C_51)=k2_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.47  tff(c_132, plain, (![A_59, B_60, A_61]: (k2_relset_1(A_59, B_60, A_61)=k2_relat_1(A_61) | ~r1_tarski(A_61, k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_6, c_104])).
% 3.30/1.47  tff(c_154, plain, (![A_62]: (k2_relset_1('#skF_1', '#skF_3', A_62)=k2_relat_1(A_62) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_132])).
% 3.30/1.47  tff(c_162, plain, (![A_13]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_13))=k2_relat_1(k7_relat_1('#skF_4', A_13)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_154])).
% 3.30/1.47  tff(c_166, plain, (![A_13]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_13))=k2_relat_1(k7_relat_1('#skF_4', A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_162])).
% 3.30/1.47  tff(c_176, plain, (![A_64, B_65, C_66]: (m1_subset_1(k2_relset_1(A_64, B_65, C_66), k1_zfmisc_1(B_65)) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.30/1.47  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.47  tff(c_310, plain, (![A_81, B_82, C_83]: (r1_tarski(k2_relset_1(A_81, B_82, C_83), B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(resolution, [status(thm)], [c_176, c_4])).
% 3.30/1.47  tff(c_350, plain, (![A_87, B_88, A_89]: (r1_tarski(k2_relset_1(A_87, B_88, A_89), B_88) | ~r1_tarski(A_89, k2_zfmisc_1(A_87, B_88)))), inference(resolution, [status(thm)], [c_6, c_310])).
% 3.30/1.47  tff(c_929, plain, (![A_148]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_148)), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', A_148), k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_166, c_350])).
% 3.30/1.47  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.47  tff(c_81, plain, (![A_47]: (r1_tarski(A_47, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_71])).
% 3.30/1.47  tff(c_47, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_40])).
% 3.30/1.47  tff(c_86, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_47])).
% 3.30/1.47  tff(c_91, plain, (![A_48]: (v1_relat_1(A_48) | ~r1_tarski(A_48, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_86])).
% 3.30/1.47  tff(c_99, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_91])).
% 3.30/1.47  tff(c_103, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_99])).
% 3.30/1.47  tff(c_323, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~r1_tarski(k2_relat_1(C_84), B_86) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.30/1.47  tff(c_243, plain, (![A_70, B_71, C_72, D_73]: (k5_relset_1(A_70, B_71, C_72, D_73)=k7_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.47  tff(c_254, plain, (![D_73]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_73)=k7_relat_1('#skF_4', D_73))), inference(resolution, [status(thm)], [c_26, c_243])).
% 3.30/1.47  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.47  tff(c_256, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_24])).
% 3.30/1.47  tff(c_328, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_323, c_256])).
% 3.30/1.47  tff(c_343, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_328])).
% 3.30/1.47  tff(c_418, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_343])).
% 3.30/1.47  tff(c_421, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_418])).
% 3.30/1.47  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_421])).
% 3.30/1.47  tff(c_426, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_343])).
% 3.30/1.47  tff(c_945, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_929, c_426])).
% 3.30/1.47  tff(c_977, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_78, c_945])).
% 3.30/1.47  tff(c_980, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_977])).
% 3.30/1.47  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_980])).
% 3.30/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.47  
% 3.30/1.47  Inference rules
% 3.30/1.47  ----------------------
% 3.30/1.47  #Ref     : 0
% 3.30/1.47  #Sup     : 198
% 3.30/1.47  #Fact    : 0
% 3.30/1.47  #Define  : 0
% 3.30/1.47  #Split   : 7
% 3.30/1.47  #Chain   : 0
% 3.30/1.47  #Close   : 0
% 3.30/1.47  
% 3.30/1.47  Ordering : KBO
% 3.30/1.47  
% 3.30/1.47  Simplification rules
% 3.30/1.47  ----------------------
% 3.30/1.47  #Subsume      : 23
% 3.30/1.47  #Demod        : 53
% 3.30/1.47  #Tautology    : 19
% 3.30/1.47  #SimpNegUnit  : 2
% 3.30/1.47  #BackRed      : 2
% 3.30/1.47  
% 3.30/1.47  #Partial instantiations: 0
% 3.30/1.47  #Strategies tried      : 1
% 3.30/1.47  
% 3.30/1.47  Timing (in seconds)
% 3.30/1.47  ----------------------
% 3.35/1.47  Preprocessing        : 0.29
% 3.35/1.47  Parsing              : 0.16
% 3.35/1.47  CNF conversion       : 0.02
% 3.35/1.47  Main loop            : 0.41
% 3.35/1.47  Inferencing          : 0.16
% 3.35/1.47  Reduction            : 0.11
% 3.35/1.47  Demodulation         : 0.08
% 3.35/1.47  BG Simplification    : 0.02
% 3.35/1.47  Subsumption          : 0.09
% 3.35/1.47  Abstraction          : 0.02
% 3.35/1.47  MUC search           : 0.00
% 3.35/1.47  Cooper               : 0.00
% 3.35/1.47  Total                : 0.73
% 3.35/1.47  Index Insertion      : 0.00
% 3.35/1.47  Index Deletion       : 0.00
% 3.35/1.47  Index Matching       : 0.00
% 3.35/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
