%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 219 expanded)
%              Number of equality atoms :    8 (  14 expanded)
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( m1_subset_1(A_67,k1_zfmisc_1(k2_zfmisc_1(B_68,C_69)))
      | ~ r1_tarski(A_67,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(B_68,C_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_388,plain,(
    ! [B_114,A_115,B_116,C_117] :
      ( m1_subset_1(k7_relat_1(B_114,A_115),k1_zfmisc_1(k2_zfmisc_1(B_116,C_117)))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(B_116,C_117)))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1084,plain,(
    ! [B_272,C_273,B_274,A_275] :
      ( k2_relset_1(B_272,C_273,k7_relat_1(B_274,A_275)) = k2_relat_1(k7_relat_1(B_274,A_275))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_zfmisc_1(B_272,C_273)))
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_388,c_16])).

tff(c_1100,plain,(
    ! [A_275] :
      ( k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_275)) = k2_relat_1(k7_relat_1('#skF_4',A_275))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1084])).

tff(c_1111,plain,(
    ! [A_279] : k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_279)) = k2_relat_1(k7_relat_1('#skF_4',A_279)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1100])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k2_relset_1(A_50,B_51,C_52),k1_zfmisc_1(B_51))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k2_relset_1(A_50,B_51,C_52),B_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_413,plain,(
    ! [B_116,C_117,B_114,A_115] :
      ( r1_tarski(k2_relset_1(B_116,C_117,k7_relat_1(B_114,A_115)),C_117)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(B_116,C_117)))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_388,c_95])).

tff(c_1120,plain,(
    ! [A_279] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_279)),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_413])).

tff(c_1137,plain,(
    ! [A_279] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_279)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26,c_1120])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_69,plain,(
    ! [B_11,A_10] :
      ( v1_relat_1(k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_291,plain,(
    ! [C_86,A_87,B_88] :
      ( m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ r1_tarski(k2_relat_1(C_86),B_88)
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_164,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k5_relset_1(A_62,B_63,C_64,D_65) = k7_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_175,plain,(
    ! [D_65] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_65) = k7_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_177,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_24])).

tff(c_312,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_291,c_177])).

tff(c_370,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_373,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_370])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_373])).

tff(c_378,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_380,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_380])).

tff(c_1142,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_1146,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1142])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.42/1.56  
% 3.42/1.56  %Foreground sorts:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Background operators:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Foreground operators:
% 3.42/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.42/1.56  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.42/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.56  
% 3.42/1.57  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.42/1.57  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.42/1.57  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.42/1.57  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.42/1.57  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.42/1.57  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 3.42/1.57  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.57  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.42/1.57  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.57  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.42/1.57  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.42/1.57  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.42/1.57  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.57  tff(c_40, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.42/1.57  tff(c_46, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_40])).
% 3.42/1.57  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 3.42/1.57  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.57  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.57  tff(c_191, plain, (![A_67, B_68, C_69, D_70]: (m1_subset_1(A_67, k1_zfmisc_1(k2_zfmisc_1(B_68, C_69))) | ~r1_tarski(A_67, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(B_68, C_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.42/1.57  tff(c_388, plain, (![B_114, A_115, B_116, C_117]: (m1_subset_1(k7_relat_1(B_114, A_115), k1_zfmisc_1(k2_zfmisc_1(B_116, C_117))) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_zfmisc_1(B_116, C_117))) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_12, c_191])).
% 3.42/1.57  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.42/1.57  tff(c_1084, plain, (![B_272, C_273, B_274, A_275]: (k2_relset_1(B_272, C_273, k7_relat_1(B_274, A_275))=k2_relat_1(k7_relat_1(B_274, A_275)) | ~m1_subset_1(B_274, k1_zfmisc_1(k2_zfmisc_1(B_272, C_273))) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_388, c_16])).
% 3.42/1.57  tff(c_1100, plain, (![A_275]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_275))=k2_relat_1(k7_relat_1('#skF_4', A_275)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1084])).
% 3.42/1.57  tff(c_1111, plain, (![A_279]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_279))=k2_relat_1(k7_relat_1('#skF_4', A_279)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1100])).
% 3.42/1.57  tff(c_82, plain, (![A_50, B_51, C_52]: (m1_subset_1(k2_relset_1(A_50, B_51, C_52), k1_zfmisc_1(B_51)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.42/1.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.57  tff(c_95, plain, (![A_50, B_51, C_52]: (r1_tarski(k2_relset_1(A_50, B_51, C_52), B_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(resolution, [status(thm)], [c_82, c_2])).
% 3.42/1.57  tff(c_413, plain, (![B_116, C_117, B_114, A_115]: (r1_tarski(k2_relset_1(B_116, C_117, k7_relat_1(B_114, A_115)), C_117) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_zfmisc_1(B_116, C_117))) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_388, c_95])).
% 3.42/1.57  tff(c_1120, plain, (![A_279]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_279)), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_413])).
% 3.42/1.57  tff(c_1137, plain, (![A_279]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_279)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26, c_1120])).
% 3.42/1.57  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.57  tff(c_55, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_4, c_40])).
% 3.42/1.57  tff(c_69, plain, (![B_11, A_10]: (v1_relat_1(k7_relat_1(B_11, A_10)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_12, c_55])).
% 3.42/1.57  tff(c_291, plain, (![C_86, A_87, B_88]: (m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~r1_tarski(k2_relat_1(C_86), B_88) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.42/1.57  tff(c_164, plain, (![A_62, B_63, C_64, D_65]: (k5_relset_1(A_62, B_63, C_64, D_65)=k7_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.57  tff(c_175, plain, (![D_65]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_65)=k7_relat_1('#skF_4', D_65))), inference(resolution, [status(thm)], [c_26, c_164])).
% 3.42/1.57  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.57  tff(c_177, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_24])).
% 3.42/1.57  tff(c_312, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_291, c_177])).
% 3.42/1.57  tff(c_370, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_312])).
% 3.42/1.57  tff(c_373, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69, c_370])).
% 3.42/1.57  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_373])).
% 3.42/1.57  tff(c_378, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_312])).
% 3.42/1.57  tff(c_380, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_378])).
% 3.42/1.57  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1137, c_380])).
% 3.42/1.57  tff(c_1142, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_378])).
% 3.42/1.57  tff(c_1146, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1142])).
% 3.42/1.57  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1146])).
% 3.42/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  
% 3.42/1.57  Inference rules
% 3.42/1.57  ----------------------
% 3.42/1.57  #Ref     : 0
% 3.42/1.57  #Sup     : 254
% 3.42/1.57  #Fact    : 0
% 3.42/1.57  #Define  : 0
% 3.42/1.57  #Split   : 4
% 3.42/1.57  #Chain   : 0
% 3.42/1.57  #Close   : 0
% 3.42/1.57  
% 3.42/1.57  Ordering : KBO
% 3.42/1.57  
% 3.42/1.57  Simplification rules
% 3.42/1.57  ----------------------
% 3.42/1.57  #Subsume      : 31
% 3.42/1.57  #Demod        : 63
% 3.42/1.57  #Tautology    : 24
% 3.42/1.57  #SimpNegUnit  : 0
% 3.42/1.57  #BackRed      : 4
% 3.42/1.57  
% 3.42/1.57  #Partial instantiations: 0
% 3.42/1.57  #Strategies tried      : 1
% 3.42/1.57  
% 3.42/1.57  Timing (in seconds)
% 3.42/1.57  ----------------------
% 3.42/1.58  Preprocessing        : 0.30
% 3.42/1.58  Parsing              : 0.17
% 3.42/1.58  CNF conversion       : 0.02
% 3.42/1.58  Main loop            : 0.50
% 3.42/1.58  Inferencing          : 0.20
% 3.42/1.58  Reduction            : 0.14
% 3.42/1.58  Demodulation         : 0.10
% 3.42/1.58  BG Simplification    : 0.03
% 3.42/1.58  Subsumption          : 0.10
% 3.42/1.58  Abstraction          : 0.03
% 3.42/1.58  MUC search           : 0.00
% 3.42/1.58  Cooper               : 0.00
% 3.42/1.58  Total                : 0.84
% 3.42/1.58  Index Insertion      : 0.00
% 3.42/1.58  Index Deletion       : 0.00
% 3.42/1.58  Index Matching       : 0.00
% 3.42/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
