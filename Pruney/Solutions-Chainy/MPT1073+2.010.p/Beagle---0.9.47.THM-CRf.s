%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 181 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 423 expanded)
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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_95,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_104,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_58,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_153,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_160,plain,(
    ! [D_91] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_91) = k9_relat_1('#skF_5',D_91) ),
    inference(resolution,[status(thm)],[c_42,c_153])).

tff(c_225,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_relset_1(A_108,B_109,C_110,A_108) = k2_relset_1(A_108,B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_225])).

tff(c_233,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_230])).

tff(c_40,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_235,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_40])).

tff(c_191,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_1'(A_100,B_101,C_102),A_100),C_102)
      | ~ r2_hidden(A_100,k9_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_funct_1(C_16,A_14) = B_15
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_253,plain,(
    ! [C_115,A_116,B_117] :
      ( k1_funct_1(C_115,'#skF_1'(A_116,B_117,C_115)) = A_116
      | ~ v1_funct_1(C_115)
      | ~ r2_hidden(A_116,k9_relat_1(C_115,B_117))
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_191,c_22])).

tff(c_255,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_235,c_253])).

tff(c_267,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_255])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_10),k1_relat_1(C_10))
      | ~ r2_hidden(A_8,k9_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_14,C_16] :
      ( r2_hidden(k4_tarski(A_14,k1_funct_1(C_16,A_14)),C_16)
      | ~ r2_hidden(A_14,k1_relat_1(C_16))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_290,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_20])).

tff(c_294,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_2'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_290])).

tff(c_296,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_299,plain,
    ( ~ r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_235,c_299])).

tff(c_305,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_59,B_2,A_1] :
      ( m1_subset_1(A_59,B_2)
      | ~ r2_hidden(A_59,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_350,plain,(
    ! [B_124] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),B_124)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_124) ) ),
    inference(resolution,[status(thm)],[c_305,c_132])).

tff(c_354,plain,(
    ! [A_6] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_6)
      | ~ v4_relat_1('#skF_5',A_6)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_350])).

tff(c_358,plain,(
    ! [A_125] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),A_125)
      | ~ v4_relat_1('#skF_5',A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_354])).

tff(c_38,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_5',E_31) != '#skF_2'
      | ~ m1_subset_1(E_31,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_386,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2'
    | ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_38])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_267,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.36/1.31  
% 2.36/1.31  %Foreground sorts:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Background operators:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Foreground operators:
% 2.36/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.36/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.31  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.36/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.31  
% 2.36/1.32  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.36/1.32  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.36/1.32  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.36/1.32  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.36/1.32  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.36/1.32  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.36/1.32  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.36/1.32  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.36/1.32  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.36/1.32  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.36/1.32  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.32  tff(c_95, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.36/1.32  tff(c_104, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_95])).
% 2.36/1.32  tff(c_58, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.32  tff(c_67, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.36/1.32  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.32  tff(c_153, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.36/1.32  tff(c_160, plain, (![D_91]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_91)=k9_relat_1('#skF_5', D_91))), inference(resolution, [status(thm)], [c_42, c_153])).
% 2.36/1.32  tff(c_225, plain, (![A_108, B_109, C_110]: (k7_relset_1(A_108, B_109, C_110, A_108)=k2_relset_1(A_108, B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.36/1.32  tff(c_230, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_225])).
% 2.36/1.32  tff(c_233, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_230])).
% 2.36/1.32  tff(c_40, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.32  tff(c_235, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_40])).
% 2.36/1.32  tff(c_191, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski('#skF_1'(A_100, B_101, C_102), A_100), C_102) | ~r2_hidden(A_100, k9_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.32  tff(c_22, plain, (![C_16, A_14, B_15]: (k1_funct_1(C_16, A_14)=B_15 | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.32  tff(c_253, plain, (![C_115, A_116, B_117]: (k1_funct_1(C_115, '#skF_1'(A_116, B_117, C_115))=A_116 | ~v1_funct_1(C_115) | ~r2_hidden(A_116, k9_relat_1(C_115, B_117)) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_191, c_22])).
% 2.36/1.32  tff(c_255, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_235, c_253])).
% 2.36/1.32  tff(c_267, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_255])).
% 2.36/1.32  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.32  tff(c_18, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_1'(A_8, B_9, C_10), k1_relat_1(C_10)) | ~r2_hidden(A_8, k9_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.32  tff(c_20, plain, (![A_14, C_16]: (r2_hidden(k4_tarski(A_14, k1_funct_1(C_16, A_14)), C_16) | ~r2_hidden(A_14, k1_relat_1(C_16)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.32  tff(c_290, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_267, c_20])).
% 2.36/1.32  tff(c_294, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_2'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_290])).
% 2.36/1.32  tff(c_296, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_294])).
% 2.36/1.32  tff(c_299, plain, (~r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.36/1.32  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_235, c_299])).
% 2.36/1.32  tff(c_305, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_294])).
% 2.36/1.32  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.32  tff(c_127, plain, (![A_59, C_60, B_61]: (m1_subset_1(A_59, C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.32  tff(c_132, plain, (![A_59, B_2, A_1]: (m1_subset_1(A_59, B_2) | ~r2_hidden(A_59, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.36/1.32  tff(c_350, plain, (![B_124]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), B_124) | ~r1_tarski(k1_relat_1('#skF_5'), B_124))), inference(resolution, [status(thm)], [c_305, c_132])).
% 2.36/1.32  tff(c_354, plain, (![A_6]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_6) | ~v4_relat_1('#skF_5', A_6) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_350])).
% 2.36/1.32  tff(c_358, plain, (![A_125]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), A_125) | ~v4_relat_1('#skF_5', A_125))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_354])).
% 2.36/1.32  tff(c_38, plain, (![E_31]: (k1_funct_1('#skF_5', E_31)!='#skF_2' | ~m1_subset_1(E_31, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.36/1.32  tff(c_386, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2' | ~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_358, c_38])).
% 2.36/1.32  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_267, c_386])).
% 2.36/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  Inference rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Ref     : 0
% 2.36/1.32  #Sup     : 79
% 2.36/1.32  #Fact    : 0
% 2.36/1.32  #Define  : 0
% 2.36/1.32  #Split   : 1
% 2.36/1.32  #Chain   : 0
% 2.36/1.32  #Close   : 0
% 2.36/1.32  
% 2.36/1.32  Ordering : KBO
% 2.36/1.32  
% 2.36/1.32  Simplification rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Subsume      : 2
% 2.36/1.32  #Demod        : 25
% 2.36/1.32  #Tautology    : 20
% 2.36/1.32  #SimpNegUnit  : 0
% 2.36/1.32  #BackRed      : 2
% 2.36/1.32  
% 2.36/1.32  #Partial instantiations: 0
% 2.36/1.32  #Strategies tried      : 1
% 2.36/1.32  
% 2.36/1.32  Timing (in seconds)
% 2.36/1.32  ----------------------
% 2.36/1.33  Preprocessing        : 0.32
% 2.36/1.33  Parsing              : 0.17
% 2.36/1.33  CNF conversion       : 0.02
% 2.36/1.33  Main loop            : 0.25
% 2.36/1.33  Inferencing          : 0.10
% 2.36/1.33  Reduction            : 0.07
% 2.36/1.33  Demodulation         : 0.05
% 2.36/1.33  BG Simplification    : 0.02
% 2.36/1.33  Subsumption          : 0.04
% 2.36/1.33  Abstraction          : 0.02
% 2.36/1.33  MUC search           : 0.00
% 2.36/1.33  Cooper               : 0.00
% 2.36/1.33  Total                : 0.61
% 2.36/1.33  Index Insertion      : 0.00
% 2.36/1.33  Index Deletion       : 0.00
% 2.36/1.33  Index Matching       : 0.00
% 2.36/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
