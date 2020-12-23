%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:49 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 110 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  100 ( 177 expanded)
%              Number of equality atoms :   21 (  25 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_63,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_255,plain,(
    ! [A_91,B_92,D_93] :
      ( r2_relset_1(A_91,B_92,D_93,D_93)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_261,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_255])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_276,plain,(
    ! [B_96,A_97] :
      ( k5_relat_1(B_96,k6_partfun1(A_97)) = B_96
      | ~ r1_tarski(k2_relat_1(B_96),A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_280,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_28,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_326,plain,(
    ! [E_111,B_108,F_109,A_107,C_106,D_110] :
      ( k4_relset_1(A_107,B_108,C_106,D_110,E_111,F_109) = k5_relat_1(E_111,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_106,D_110)))
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_392,plain,(
    ! [A_116,B_117,A_118,E_119] :
      ( k4_relset_1(A_116,B_117,A_118,A_118,E_119,k6_partfun1(A_118)) = k5_relat_1(E_119,k6_partfun1(A_118))
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(resolution,[status(thm)],[c_28,c_326])).

tff(c_398,plain,(
    ! [A_118] : k4_relset_1('#skF_1','#skF_2',A_118,A_118,'#skF_3',k6_partfun1(A_118)) = k5_relat_1('#skF_3',k6_partfun1(A_118)) ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_125,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_131,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_125])).

tff(c_83,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_91,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_99,plain,(
    ! [B_51,A_52] :
      ( k7_relat_1(B_51,A_52) = B_51
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_99])).

tff(c_111,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_105])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_partfun1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_14])).

tff(c_178,plain,(
    ! [B_70,E_73,F_71,C_68,D_72,A_69] :
      ( k4_relset_1(A_69,B_70,C_68,D_72,E_73,F_71) = k5_relat_1(E_73,F_71)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_68,D_72)))
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_185,plain,(
    ! [A_74,B_75,E_76] :
      ( k4_relset_1(A_74,B_75,'#skF_1','#skF_2',E_76,'#skF_3') = k5_relat_1(E_76,'#skF_3')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_192,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_198,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_72])).

tff(c_210,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_198])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_131,c_111,c_210])).

tff(c_214,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_399,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_214])).

tff(c_411,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_399])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_71,c_261,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:50 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.36  
% 2.28/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.36  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.36  
% 2.28/1.36  %Foreground sorts:
% 2.28/1.36  
% 2.28/1.36  
% 2.28/1.36  %Background operators:
% 2.28/1.36  
% 2.28/1.36  
% 2.28/1.36  %Foreground operators:
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.28/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.36  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.28/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.36  
% 2.57/1.38  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.57/1.38  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.57/1.38  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.57/1.38  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.57/1.38  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.57/1.38  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.57/1.38  tff(f_82, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.57/1.38  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.57/1.38  tff(f_80, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.57/1.38  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.57/1.38  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.57/1.38  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.57/1.38  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.38  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.57/1.38  tff(c_49, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.38  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.57/1.38  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 2.57/1.38  tff(c_63, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.38  tff(c_71, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.57/1.38  tff(c_255, plain, (![A_91, B_92, D_93]: (r2_relset_1(A_91, B_92, D_93, D_93) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.38  tff(c_261, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_255])).
% 2.57/1.38  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.38  tff(c_30, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.57/1.38  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.38  tff(c_276, plain, (![B_96, A_97]: (k5_relat_1(B_96, k6_partfun1(A_97))=B_96 | ~r1_tarski(k2_relat_1(B_96), A_97) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.57/1.38  tff(c_280, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_276])).
% 2.57/1.38  tff(c_28, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.38  tff(c_326, plain, (![E_111, B_108, F_109, A_107, C_106, D_110]: (k4_relset_1(A_107, B_108, C_106, D_110, E_111, F_109)=k5_relat_1(E_111, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_106, D_110))) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.38  tff(c_392, plain, (![A_116, B_117, A_118, E_119]: (k4_relset_1(A_116, B_117, A_118, A_118, E_119, k6_partfun1(A_118))=k5_relat_1(E_119, k6_partfun1(A_118)) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(resolution, [status(thm)], [c_28, c_326])).
% 2.57/1.38  tff(c_398, plain, (![A_118]: (k4_relset_1('#skF_1', '#skF_2', A_118, A_118, '#skF_3', k6_partfun1(A_118))=k5_relat_1('#skF_3', k6_partfun1(A_118)))), inference(resolution, [status(thm)], [c_34, c_392])).
% 2.57/1.38  tff(c_125, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.38  tff(c_131, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_125])).
% 2.57/1.38  tff(c_83, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.38  tff(c_91, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_83])).
% 2.57/1.38  tff(c_99, plain, (![B_51, A_52]: (k7_relat_1(B_51, A_52)=B_51 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.57/1.38  tff(c_105, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_91, c_99])).
% 2.57/1.38  tff(c_111, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_105])).
% 2.57/1.38  tff(c_14, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.38  tff(c_35, plain, (![A_12, B_13]: (k5_relat_1(k6_partfun1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_14])).
% 2.57/1.38  tff(c_178, plain, (![B_70, E_73, F_71, C_68, D_72, A_69]: (k4_relset_1(A_69, B_70, C_68, D_72, E_73, F_71)=k5_relat_1(E_73, F_71) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_68, D_72))) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.38  tff(c_185, plain, (![A_74, B_75, E_76]: (k4_relset_1(A_74, B_75, '#skF_1', '#skF_2', E_76, '#skF_3')=k5_relat_1(E_76, '#skF_3') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.57/1.38  tff(c_192, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_185])).
% 2.57/1.38  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.57/1.38  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.57/1.38  tff(c_198, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_72])).
% 2.57/1.38  tff(c_210, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35, c_198])).
% 2.57/1.38  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_131, c_111, c_210])).
% 2.57/1.38  tff(c_214, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.57/1.38  tff(c_399, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_214])).
% 2.57/1.38  tff(c_411, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_280, c_399])).
% 2.57/1.38  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_71, c_261, c_411])).
% 2.57/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  Inference rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Ref     : 0
% 2.57/1.38  #Sup     : 78
% 2.57/1.38  #Fact    : 0
% 2.57/1.38  #Define  : 0
% 2.57/1.38  #Split   : 2
% 2.57/1.38  #Chain   : 0
% 2.57/1.38  #Close   : 0
% 2.57/1.38  
% 2.57/1.38  Ordering : KBO
% 2.57/1.38  
% 2.57/1.38  Simplification rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Subsume      : 2
% 2.57/1.38  #Demod        : 47
% 2.57/1.38  #Tautology    : 43
% 2.57/1.38  #SimpNegUnit  : 0
% 2.57/1.38  #BackRed      : 4
% 2.57/1.38  
% 2.57/1.38  #Partial instantiations: 0
% 2.57/1.38  #Strategies tried      : 1
% 2.57/1.38  
% 2.57/1.38  Timing (in seconds)
% 2.57/1.38  ----------------------
% 2.57/1.38  Preprocessing        : 0.33
% 2.57/1.38  Parsing              : 0.18
% 2.57/1.38  CNF conversion       : 0.02
% 2.57/1.38  Main loop            : 0.24
% 2.57/1.38  Inferencing          : 0.10
% 2.57/1.38  Reduction            : 0.08
% 2.57/1.38  Demodulation         : 0.06
% 2.57/1.38  BG Simplification    : 0.02
% 2.57/1.38  Subsumption          : 0.03
% 2.57/1.38  Abstraction          : 0.02
% 2.57/1.38  MUC search           : 0.00
% 2.57/1.38  Cooper               : 0.00
% 2.57/1.38  Total                : 0.61
% 2.57/1.38  Index Insertion      : 0.00
% 2.57/1.38  Index Deletion       : 0.00
% 2.57/1.38  Index Matching       : 0.00
% 2.57/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
