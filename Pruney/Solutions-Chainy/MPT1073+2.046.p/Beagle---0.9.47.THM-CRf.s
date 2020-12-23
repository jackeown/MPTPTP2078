%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 202 expanded)
%              Number of leaves         :   37 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 465 expanded)
%              Number of equality atoms :   16 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_110,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_163,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_170,plain,(
    ! [D_92] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_92) = k9_relat_1('#skF_5',D_92) ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_201,plain,(
    ! [A_101,B_102,C_103] :
      ( k7_relset_1(A_101,B_102,C_103,A_101) = k2_relset_1(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_206,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_201])).

tff(c_209,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_206])).

tff(c_42,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_211,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_42])).

tff(c_180,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden(k4_tarski('#skF_1'(A_94,B_95,C_96),A_94),C_96)
      | ~ r2_hidden(A_94,k9_relat_1(C_96,B_95))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_263,plain,(
    ! [C_116,A_117,B_118] :
      ( k1_funct_1(C_116,'#skF_1'(A_117,B_118,C_116)) = A_117
      | ~ v1_funct_1(C_116)
      | ~ r2_hidden(A_117,k9_relat_1(C_116,B_118))
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_180,c_26])).

tff(c_268,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_263])).

tff(c_278,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_268])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_284,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_24])).

tff(c_288,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_284])).

tff(c_290,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_293,plain,
    ( ~ r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_211,c_293])).

tff(c_299,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [A_58,C_59,B_60] :
      ( m1_subset_1(A_58,C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_58,B_2,A_1] :
      ( m1_subset_1(A_58,B_2)
      | ~ r2_hidden(A_58,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_318,plain,(
    ! [B_119] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),B_119)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_119) ) ),
    inference(resolution,[status(thm)],[c_299,c_125])).

tff(c_322,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_9)
      | ~ v4_relat_1('#skF_5',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_318])).

tff(c_326,plain,(
    ! [A_120] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_120)
      | ~ v4_relat_1('#skF_5',A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_322])).

tff(c_40,plain,(
    ! [E_33] :
      ( k1_funct_1('#skF_5',E_33) != '#skF_2'
      | ~ m1_subset_1(E_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_358,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2'
    | ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_326,c_40])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_278,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.35  
% 2.46/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.64/1.35  
% 2.64/1.35  %Foreground sorts:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Background operators:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Foreground operators:
% 2.64/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.64/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.64/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.64/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.64/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.64/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.64/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.64/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.35  
% 2.64/1.37  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.64/1.37  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.64/1.37  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.64/1.37  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.64/1.37  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.64/1.37  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.64/1.37  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.64/1.37  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.64/1.37  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.64/1.37  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.37  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.64/1.37  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.37  tff(c_110, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.64/1.37  tff(c_119, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_110])).
% 2.64/1.37  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.37  tff(c_61, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.37  tff(c_67, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.64/1.37  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_67])).
% 2.64/1.37  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.37  tff(c_163, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.64/1.37  tff(c_170, plain, (![D_92]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_92)=k9_relat_1('#skF_5', D_92))), inference(resolution, [status(thm)], [c_44, c_163])).
% 2.64/1.37  tff(c_201, plain, (![A_101, B_102, C_103]: (k7_relset_1(A_101, B_102, C_103, A_101)=k2_relset_1(A_101, B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.64/1.37  tff(c_206, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_201])).
% 2.64/1.37  tff(c_209, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_206])).
% 2.64/1.37  tff(c_42, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.37  tff(c_211, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_42])).
% 2.64/1.37  tff(c_180, plain, (![A_94, B_95, C_96]: (r2_hidden(k4_tarski('#skF_1'(A_94, B_95, C_96), A_94), C_96) | ~r2_hidden(A_94, k9_relat_1(C_96, B_95)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.37  tff(c_26, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.37  tff(c_263, plain, (![C_116, A_117, B_118]: (k1_funct_1(C_116, '#skF_1'(A_117, B_118, C_116))=A_117 | ~v1_funct_1(C_116) | ~r2_hidden(A_117, k9_relat_1(C_116, B_118)) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_180, c_26])).
% 2.64/1.37  tff(c_268, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_211, c_263])).
% 2.64/1.37  tff(c_278, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_268])).
% 2.64/1.37  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.37  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.37  tff(c_24, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.37  tff(c_284, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_278, c_24])).
% 2.64/1.37  tff(c_288, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_284])).
% 2.64/1.37  tff(c_290, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_288])).
% 2.64/1.37  tff(c_293, plain, (~r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_290])).
% 2.64/1.37  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_211, c_293])).
% 2.64/1.37  tff(c_299, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_288])).
% 2.64/1.37  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.37  tff(c_120, plain, (![A_58, C_59, B_60]: (m1_subset_1(A_58, C_59) | ~m1_subset_1(B_60, k1_zfmisc_1(C_59)) | ~r2_hidden(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.37  tff(c_125, plain, (![A_58, B_2, A_1]: (m1_subset_1(A_58, B_2) | ~r2_hidden(A_58, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.64/1.37  tff(c_318, plain, (![B_119]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), B_119) | ~r1_tarski(k1_relat_1('#skF_5'), B_119))), inference(resolution, [status(thm)], [c_299, c_125])).
% 2.64/1.37  tff(c_322, plain, (![A_9]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_9) | ~v4_relat_1('#skF_5', A_9) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_318])).
% 2.64/1.37  tff(c_326, plain, (![A_120]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_120) | ~v4_relat_1('#skF_5', A_120))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_322])).
% 2.64/1.37  tff(c_40, plain, (![E_33]: (k1_funct_1('#skF_5', E_33)!='#skF_2' | ~m1_subset_1(E_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.37  tff(c_358, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2' | ~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_326, c_40])).
% 2.64/1.37  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_278, c_358])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 68
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 2
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 2
% 2.64/1.37  #Demod        : 28
% 2.64/1.37  #Tautology    : 20
% 2.64/1.37  #SimpNegUnit  : 0
% 2.64/1.37  #BackRed      : 2
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.37  Preprocessing        : 0.31
% 2.64/1.37  Parsing              : 0.16
% 2.64/1.37  CNF conversion       : 0.02
% 2.64/1.37  Main loop            : 0.25
% 2.64/1.37  Inferencing          : 0.10
% 2.64/1.37  Reduction            : 0.07
% 2.64/1.37  Demodulation         : 0.05
% 2.64/1.37  BG Simplification    : 0.02
% 2.64/1.37  Subsumption          : 0.04
% 2.64/1.37  Abstraction          : 0.02
% 2.64/1.37  MUC search           : 0.00
% 2.64/1.37  Cooper               : 0.00
% 2.64/1.37  Total                : 0.59
% 2.64/1.37  Index Insertion      : 0.00
% 2.64/1.37  Index Deletion       : 0.00
% 2.64/1.37  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
