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
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 166 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 289 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_35,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_117,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_117])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ! [A_4,A_49,B_50] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_144,plain,(
    ! [A_66] :
      ( v1_relat_1(A_66)
      | ~ r1_tarski(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_130,c_84])).

tff(c_152,plain,(
    ! [A_18] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_18))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_144])).

tff(c_160,plain,(
    ! [A_18] : v1_relat_1(k7_relat_1('#skF_4',A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_152])).

tff(c_127,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_117])).

tff(c_294,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k2_relat_1(A_93),k2_relat_1(B_94))
      | ~ r1_tarski(A_93,B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_11,B_12)),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    ! [A_62,B_12,A_11] :
      ( r1_tarski(A_62,B_12)
      | ~ r1_tarski(A_62,k2_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_12,c_117])).

tff(c_300,plain,(
    ! [A_93,B_12,A_11] :
      ( r1_tarski(k2_relat_1(A_93),B_12)
      | ~ r1_tarski(A_93,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_294,c_129])).

tff(c_480,plain,(
    ! [A_135,B_136,A_137] :
      ( r1_tarski(k2_relat_1(A_135),B_136)
      | ~ r1_tarski(A_135,k2_zfmisc_1(A_137,B_136))
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_300])).

tff(c_520,plain,(
    ! [A_62] :
      ( r1_tarski(k2_relat_1(A_62),'#skF_3')
      | ~ v1_relat_1(A_62)
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_480])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_531,plain,(
    ! [C_138,A_139,B_140] :
      ( m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ r1_tarski(k2_relat_1(C_138),B_140)
      | ~ r1_tarski(k1_relat_1(C_138),A_139)
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_366,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k5_relset_1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_373,plain,(
    ! [D_121] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_121) = k7_relat_1('#skF_4',D_121) ),
    inference(resolution,[status(thm)],[c_30,c_366])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_375,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_28])).

tff(c_534,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_531,c_375])).

tff(c_548,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_534])).

tff(c_886,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_889,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_886])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_889])).

tff(c_894,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_898,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_520,c_894])).

tff(c_901,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_898])).

tff(c_904,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_901])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n019.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:42:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/2.04  
% 4.25/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/2.04  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.25/2.04  
% 4.25/2.04  %Foreground sorts:
% 4.25/2.04  
% 4.25/2.04  
% 4.25/2.04  %Background operators:
% 4.25/2.04  
% 4.25/2.04  
% 4.25/2.04  %Foreground operators:
% 4.25/2.04  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 4.25/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.25/2.04  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.25/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.25/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.25/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.25/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.25/2.04  tff('#skF_1', type, '#skF_1': $i).
% 4.25/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.25/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.25/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.25/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.25/2.04  tff('#skF_4', type, '#skF_4': $i).
% 4.25/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.25/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.25/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.25/2.04  
% 4.37/2.07  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.37/2.07  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 4.37/2.07  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.37/2.07  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.37/2.07  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.37/2.07  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.37/2.07  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.37/2.07  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.37/2.07  tff(f_46, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 4.37/2.07  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.37/2.07  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.37/2.07  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 4.37/2.07  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.37/2.07  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/2.07  tff(c_44, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.37/2.07  tff(c_50, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_44])).
% 4.37/2.07  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 4.37/2.07  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.37/2.07  tff(c_35, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/2.07  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_35])).
% 4.37/2.07  tff(c_117, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/2.07  tff(c_130, plain, (![A_65]: (r1_tarski(A_65, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_117])).
% 4.37/2.07  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/2.07  tff(c_76, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.37/2.07  tff(c_84, plain, (![A_4, A_49, B_50]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_49, B_50)))), inference(resolution, [status(thm)], [c_6, c_76])).
% 4.37/2.07  tff(c_144, plain, (![A_66]: (v1_relat_1(A_66) | ~r1_tarski(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_130, c_84])).
% 4.37/2.07  tff(c_152, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_144])).
% 4.37/2.07  tff(c_160, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_152])).
% 4.37/2.07  tff(c_127, plain, (![A_62]: (r1_tarski(A_62, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_117])).
% 4.37/2.07  tff(c_294, plain, (![A_93, B_94]: (r1_tarski(k2_relat_1(A_93), k2_relat_1(B_94)) | ~r1_tarski(A_93, B_94) | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.37/2.07  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_11, B_12)), B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.37/2.07  tff(c_129, plain, (![A_62, B_12, A_11]: (r1_tarski(A_62, B_12) | ~r1_tarski(A_62, k2_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_12, c_117])).
% 4.37/2.07  tff(c_300, plain, (![A_93, B_12, A_11]: (r1_tarski(k2_relat_1(A_93), B_12) | ~r1_tarski(A_93, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_294, c_129])).
% 4.37/2.07  tff(c_480, plain, (![A_135, B_136, A_137]: (r1_tarski(k2_relat_1(A_135), B_136) | ~r1_tarski(A_135, k2_zfmisc_1(A_137, B_136)) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_300])).
% 4.37/2.07  tff(c_520, plain, (![A_62]: (r1_tarski(k2_relat_1(A_62), '#skF_3') | ~v1_relat_1(A_62) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_127, c_480])).
% 4.37/2.07  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.37/2.07  tff(c_531, plain, (![C_138, A_139, B_140]: (m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~r1_tarski(k2_relat_1(C_138), B_140) | ~r1_tarski(k1_relat_1(C_138), A_139) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/2.07  tff(c_366, plain, (![A_118, B_119, C_120, D_121]: (k5_relset_1(A_118, B_119, C_120, D_121)=k7_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/2.07  tff(c_373, plain, (![D_121]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_121)=k7_relat_1('#skF_4', D_121))), inference(resolution, [status(thm)], [c_30, c_366])).
% 4.37/2.07  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/2.07  tff(c_375, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_28])).
% 4.37/2.07  tff(c_534, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_531, c_375])).
% 4.37/2.07  tff(c_548, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_534])).
% 4.37/2.07  tff(c_886, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_548])).
% 4.37/2.07  tff(c_889, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_886])).
% 4.37/2.07  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_889])).
% 4.37/2.07  tff(c_894, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_548])).
% 4.37/2.07  tff(c_898, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_520, c_894])).
% 4.37/2.07  tff(c_901, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_898])).
% 4.37/2.07  tff(c_904, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_901])).
% 4.37/2.07  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_904])).
% 4.37/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/2.07  
% 4.37/2.07  Inference rules
% 4.37/2.07  ----------------------
% 4.37/2.07  #Ref     : 0
% 4.37/2.07  #Sup     : 186
% 4.37/2.07  #Fact    : 0
% 4.37/2.07  #Define  : 0
% 4.37/2.07  #Split   : 4
% 4.37/2.07  #Chain   : 0
% 4.37/2.07  #Close   : 0
% 4.37/2.07  
% 4.37/2.07  Ordering : KBO
% 4.37/2.07  
% 4.37/2.07  Simplification rules
% 4.37/2.07  ----------------------
% 4.37/2.07  #Subsume      : 15
% 4.37/2.07  #Demod        : 34
% 4.37/2.07  #Tautology    : 10
% 4.37/2.07  #SimpNegUnit  : 0
% 4.37/2.07  #BackRed      : 2
% 4.37/2.07  
% 4.37/2.07  #Partial instantiations: 0
% 4.37/2.07  #Strategies tried      : 1
% 4.37/2.07  
% 4.37/2.07  Timing (in seconds)
% 4.37/2.07  ----------------------
% 4.37/2.07  Preprocessing        : 0.48
% 4.37/2.07  Parsing              : 0.25
% 4.37/2.07  CNF conversion       : 0.03
% 4.37/2.07  Main loop            : 0.72
% 4.37/2.07  Inferencing          : 0.27
% 4.37/2.07  Reduction            : 0.21
% 4.37/2.08  Demodulation         : 0.15
% 4.37/2.08  BG Simplification    : 0.03
% 4.37/2.08  Subsumption          : 0.15
% 4.37/2.08  Abstraction          : 0.04
% 4.37/2.08  MUC search           : 0.00
% 4.37/2.08  Cooper               : 0.00
% 4.37/2.08  Total                : 1.25
% 4.37/2.08  Index Insertion      : 0.00
% 4.37/2.08  Index Deletion       : 0.00
% 4.37/2.08  Index Matching       : 0.00
% 4.37/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
