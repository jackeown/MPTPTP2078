%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:47 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 171 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_75,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_55,plain,(
    ! [C_36,B_37,A_38] :
      ( v5_relat_1(C_36,B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_285,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_relset_1(A_93,B_94,C_95,C_95)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_297,plain,(
    ! [C_100] :
      ( r2_relset_1('#skF_1','#skF_2',C_100,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_285])).

tff(c_300,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_297])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [B_87,A_88] :
      ( k5_relat_1(B_87,k6_partfun1(A_88)) = B_87
      | ~ r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_257,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_253])).

tff(c_24,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_301,plain,(
    ! [B_103,A_106,E_105,F_104,C_101,D_102] :
      ( k4_relset_1(A_106,B_103,C_101,D_102,E_105,F_104) = k5_relat_1(E_105,F_104)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_101,D_102)))
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_336,plain,(
    ! [A_111,B_112,A_113,E_114] :
      ( k4_relset_1(A_111,B_112,A_113,A_113,E_114,k6_partfun1(A_113)) = k5_relat_1(E_114,k6_partfun1(A_113))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(resolution,[status(thm)],[c_24,c_301])).

tff(c_342,plain,(
    ! [A_113] : k4_relset_1('#skF_1','#skF_2',A_113,A_113,'#skF_3',k6_partfun1(A_113)) = k5_relat_1('#skF_3',k6_partfun1(A_113)) ),
    inference(resolution,[status(thm)],[c_30,c_336])).

tff(c_148,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( r2_relset_1(A_57,B_58,C_59,C_59)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_160,plain,(
    ! [C_64] :
      ( r2_relset_1('#skF_1','#skF_2',C_64,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_163,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_81,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_95,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_partfun1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_164,plain,(
    ! [D_66,F_68,B_67,A_70,C_65,E_69] :
      ( k4_relset_1(A_70,B_67,C_65,D_66,E_69,F_68) = k5_relat_1(E_69,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_65,D_66)))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171,plain,(
    ! [A_71,B_72,E_73] :
      ( k4_relset_1(A_71,B_72,'#skF_1','#skF_2',E_73,'#skF_3') = k5_relat_1(E_73,'#skF_3')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_178,plain,(
    ! [A_25] : k4_relset_1(A_25,A_25,'#skF_1','#skF_2',k6_partfun1(A_25),'#skF_3') = k5_relat_1(k6_partfun1(A_25),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_28,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_184,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_64])).

tff(c_196,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_184])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_163,c_95,c_196])).

tff(c_200,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_343,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_200])).

tff(c_355,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_343])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_63,c_300,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.32  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.32  
% 2.20/1.32  %Foreground sorts:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Background operators:
% 2.20/1.32  
% 2.20/1.32  
% 2.20/1.32  %Foreground operators:
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.20/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.20/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.20/1.32  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.20/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.20/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.20/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.20/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.20/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.32  
% 2.20/1.33  tff(f_82, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.20/1.33  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.20/1.33  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.20/1.33  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.20/1.33  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.20/1.33  tff(f_75, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.20/1.33  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.20/1.33  tff(f_73, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.20/1.33  tff(f_63, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.20/1.33  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.20/1.33  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.20/1.33  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.33  tff(c_44, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.33  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_44])).
% 2.20/1.33  tff(c_55, plain, (![C_36, B_37, A_38]: (v5_relat_1(C_36, B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.33  tff(c_63, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_55])).
% 2.20/1.33  tff(c_285, plain, (![A_93, B_94, C_95, D_96]: (r2_relset_1(A_93, B_94, C_95, C_95) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.33  tff(c_297, plain, (![C_100]: (r2_relset_1('#skF_1', '#skF_2', C_100, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_285])).
% 2.20/1.33  tff(c_300, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_297])).
% 2.20/1.33  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.33  tff(c_26, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.20/1.33  tff(c_8, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~r1_tarski(k2_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.33  tff(c_253, plain, (![B_87, A_88]: (k5_relat_1(B_87, k6_partfun1(A_88))=B_87 | ~r1_tarski(k2_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.20/1.33  tff(c_257, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_253])).
% 2.20/1.33  tff(c_24, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.33  tff(c_301, plain, (![B_103, A_106, E_105, F_104, C_101, D_102]: (k4_relset_1(A_106, B_103, C_101, D_102, E_105, F_104)=k5_relat_1(E_105, F_104) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_101, D_102))) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_103))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.33  tff(c_336, plain, (![A_111, B_112, A_113, E_114]: (k4_relset_1(A_111, B_112, A_113, A_113, E_114, k6_partfun1(A_113))=k5_relat_1(E_114, k6_partfun1(A_113)) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(resolution, [status(thm)], [c_24, c_301])).
% 2.20/1.33  tff(c_342, plain, (![A_113]: (k4_relset_1('#skF_1', '#skF_2', A_113, A_113, '#skF_3', k6_partfun1(A_113))=k5_relat_1('#skF_3', k6_partfun1(A_113)))), inference(resolution, [status(thm)], [c_30, c_336])).
% 2.20/1.33  tff(c_148, plain, (![A_57, B_58, C_59, D_60]: (r2_relset_1(A_57, B_58, C_59, C_59) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.20/1.33  tff(c_160, plain, (![C_64]: (r2_relset_1('#skF_1', '#skF_2', C_64, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_30, c_148])).
% 2.20/1.33  tff(c_163, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_160])).
% 2.20/1.33  tff(c_81, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.33  tff(c_89, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_81])).
% 2.20/1.33  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.33  tff(c_92, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89, c_6])).
% 2.20/1.33  tff(c_95, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_92])).
% 2.20/1.33  tff(c_10, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.33  tff(c_31, plain, (![A_7, B_8]: (k5_relat_1(k6_partfun1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.20/1.33  tff(c_164, plain, (![D_66, F_68, B_67, A_70, C_65, E_69]: (k4_relset_1(A_70, B_67, C_65, D_66, E_69, F_68)=k5_relat_1(E_69, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_65, D_66))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_67))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.33  tff(c_171, plain, (![A_71, B_72, E_73]: (k4_relset_1(A_71, B_72, '#skF_1', '#skF_2', E_73, '#skF_3')=k5_relat_1(E_73, '#skF_3') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(resolution, [status(thm)], [c_30, c_164])).
% 2.20/1.33  tff(c_178, plain, (![A_25]: (k4_relset_1(A_25, A_25, '#skF_1', '#skF_2', k6_partfun1(A_25), '#skF_3')=k5_relat_1(k6_partfun1(A_25), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_171])).
% 2.20/1.33  tff(c_28, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.20/1.33  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.20/1.33  tff(c_184, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_64])).
% 2.20/1.33  tff(c_196, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31, c_184])).
% 2.20/1.33  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_163, c_95, c_196])).
% 2.20/1.33  tff(c_200, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.20/1.33  tff(c_343, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_200])).
% 2.20/1.33  tff(c_355, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_257, c_343])).
% 2.20/1.33  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_63, c_300, c_355])).
% 2.20/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  Inference rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Ref     : 0
% 2.20/1.33  #Sup     : 71
% 2.20/1.33  #Fact    : 0
% 2.20/1.33  #Define  : 0
% 2.20/1.33  #Split   : 1
% 2.20/1.33  #Chain   : 0
% 2.20/1.33  #Close   : 0
% 2.20/1.33  
% 2.20/1.33  Ordering : KBO
% 2.20/1.33  
% 2.20/1.33  Simplification rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Subsume      : 2
% 2.20/1.33  #Demod        : 28
% 2.20/1.33  #Tautology    : 33
% 2.20/1.33  #SimpNegUnit  : 0
% 2.20/1.33  #BackRed      : 3
% 2.20/1.33  
% 2.20/1.33  #Partial instantiations: 0
% 2.20/1.33  #Strategies tried      : 1
% 2.20/1.33  
% 2.20/1.33  Timing (in seconds)
% 2.20/1.33  ----------------------
% 2.60/1.34  Preprocessing        : 0.30
% 2.60/1.34  Parsing              : 0.16
% 2.60/1.34  CNF conversion       : 0.02
% 2.60/1.34  Main loop            : 0.25
% 2.60/1.34  Inferencing          : 0.10
% 2.60/1.34  Reduction            : 0.08
% 2.60/1.34  Demodulation         : 0.05
% 2.60/1.34  BG Simplification    : 0.01
% 2.60/1.34  Subsumption          : 0.03
% 2.60/1.34  Abstraction          : 0.02
% 2.60/1.34  MUC search           : 0.00
% 2.60/1.34  Cooper               : 0.00
% 2.60/1.34  Total                : 0.59
% 2.60/1.34  Index Insertion      : 0.00
% 2.60/1.34  Index Deletion       : 0.00
% 2.60/1.34  Index Matching       : 0.00
% 2.60/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
