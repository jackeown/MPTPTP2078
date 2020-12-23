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
% DateTime   : Thu Dec  3 10:07:31 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 162 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 288 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_51])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_58)
      | ~ r1_tarski(A_56,B_58)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_381,plain,(
    ! [A_107,B_108,B_109,B_110] :
      ( r2_hidden('#skF_1'(A_107,B_108),B_109)
      | ~ r1_tarski(B_110,B_109)
      | ~ r1_tarski(A_107,B_110)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_502,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_1'(A_120,B_121),k2_zfmisc_1('#skF_2','#skF_4'))
      | ~ r1_tarski(A_120,'#skF_5')
      | r1_tarski(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_42,c_381])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_510,plain,(
    ! [A_120] :
      ( ~ r1_tarski(A_120,'#skF_5')
      | r1_tarski(A_120,k2_zfmisc_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_502,c_4])).

tff(c_524,plain,(
    ! [A_122] :
      ( ~ r1_tarski(A_122,'#skF_5')
      | r1_tarski(A_122,k2_zfmisc_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_502,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109,plain,(
    ! [A_59,B_60,A_6] :
      ( k2_relset_1(A_59,B_60,A_6) = k2_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_611,plain,(
    ! [A_130] :
      ( k2_relset_1('#skF_2','#skF_4',A_130) = k2_relat_1(A_130)
      | ~ r1_tarski(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_524,c_109])).

tff(c_631,plain,(
    ! [A_15] :
      ( k2_relset_1('#skF_2','#skF_4',k7_relat_1('#skF_5',A_15)) = k2_relat_1(k7_relat_1('#skF_5',A_15))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_611])).

tff(c_670,plain,(
    ! [A_136] : k2_relset_1('#skF_2','#skF_4',k7_relat_1('#skF_5',A_136)) = k2_relat_1(k7_relat_1('#skF_5',A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_631])).

tff(c_147,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_relset_1(A_67,B_68,C_69),k1_zfmisc_1(B_68))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_209,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k2_relset_1(A_75,B_76,C_77),B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_147,c_8])).

tff(c_219,plain,(
    ! [A_75,B_76,A_6] :
      ( r1_tarski(k2_relset_1(A_75,B_76,A_6),B_76)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_1172,plain,(
    ! [A_189] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_189)),'#skF_4')
      | ~ r1_tarski(k7_relat_1('#skF_5',A_189),k2_zfmisc_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_219])).

tff(c_60,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(A_44)
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_74,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_242,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ r1_tarski(k2_relat_1(C_81),B_83)
      | ~ r1_tarski(k1_relat_1(C_81),A_82)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_177,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k5_relset_1(A_70,B_71,C_72,D_73) = k7_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_188,plain,(
    ! [D_73] : k5_relset_1('#skF_2','#skF_4','#skF_5',D_73) = k7_relat_1('#skF_5',D_73) ),
    inference(resolution,[status(thm)],[c_30,c_177])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_195,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_28])).

tff(c_260,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_242,c_195])).

tff(c_312,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_315,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_315])).

tff(c_320,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_323,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_1197,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1172,c_323])).

tff(c_1202,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_510,c_1197])).

tff(c_1205,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1202])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1205])).

tff(c_1210,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_1214,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_1210])).

tff(c_1218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  
% 3.36/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.36/1.58  
% 3.36/1.58  %Foreground sorts:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Background operators:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Foreground operators:
% 3.36/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.36/1.58  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.36/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.58  
% 3.36/1.60  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.60  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 3.36/1.60  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.36/1.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.36/1.60  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.36/1.60  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.36/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.36/1.60  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.36/1.60  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.36/1.60  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.36/1.60  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.36/1.60  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.60  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.60  tff(c_45, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.60  tff(c_51, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_45])).
% 3.36/1.60  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_51])).
% 3.36/1.60  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.60  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.60  tff(c_34, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.60  tff(c_42, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 3.36/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_87, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_92, plain, (![A_56, B_57, B_58]: (r2_hidden('#skF_1'(A_56, B_57), B_58) | ~r1_tarski(A_56, B_58) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_6, c_87])).
% 3.36/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_381, plain, (![A_107, B_108, B_109, B_110]: (r2_hidden('#skF_1'(A_107, B_108), B_109) | ~r1_tarski(B_110, B_109) | ~r1_tarski(A_107, B_110) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_92, c_2])).
% 3.36/1.60  tff(c_502, plain, (![A_120, B_121]: (r2_hidden('#skF_1'(A_120, B_121), k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski(A_120, '#skF_5') | r1_tarski(A_120, B_121))), inference(resolution, [status(thm)], [c_42, c_381])).
% 3.36/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.60  tff(c_510, plain, (![A_120]: (~r1_tarski(A_120, '#skF_5') | r1_tarski(A_120, k2_zfmisc_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_502, c_4])).
% 3.36/1.60  tff(c_524, plain, (![A_122]: (~r1_tarski(A_122, '#skF_5') | r1_tarski(A_122, k2_zfmisc_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_502, c_4])).
% 3.36/1.60  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.60  tff(c_101, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.60  tff(c_109, plain, (![A_59, B_60, A_6]: (k2_relset_1(A_59, B_60, A_6)=k2_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_10, c_101])).
% 3.36/1.60  tff(c_611, plain, (![A_130]: (k2_relset_1('#skF_2', '#skF_4', A_130)=k2_relat_1(A_130) | ~r1_tarski(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_524, c_109])).
% 3.36/1.60  tff(c_631, plain, (![A_15]: (k2_relset_1('#skF_2', '#skF_4', k7_relat_1('#skF_5', A_15))=k2_relat_1(k7_relat_1('#skF_5', A_15)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_611])).
% 3.36/1.60  tff(c_670, plain, (![A_136]: (k2_relset_1('#skF_2', '#skF_4', k7_relat_1('#skF_5', A_136))=k2_relat_1(k7_relat_1('#skF_5', A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_631])).
% 3.36/1.60  tff(c_147, plain, (![A_67, B_68, C_69]: (m1_subset_1(k2_relset_1(A_67, B_68, C_69), k1_zfmisc_1(B_68)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.60  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.60  tff(c_209, plain, (![A_75, B_76, C_77]: (r1_tarski(k2_relset_1(A_75, B_76, C_77), B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_147, c_8])).
% 3.36/1.60  tff(c_219, plain, (![A_75, B_76, A_6]: (r1_tarski(k2_relset_1(A_75, B_76, A_6), B_76) | ~r1_tarski(A_6, k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_10, c_209])).
% 3.36/1.60  tff(c_1172, plain, (![A_189]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_189)), '#skF_4') | ~r1_tarski(k7_relat_1('#skF_5', A_189), k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_670, c_219])).
% 3.36/1.60  tff(c_60, plain, (![A_44, B_45]: (v1_relat_1(A_44) | ~v1_relat_1(B_45) | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_10, c_45])).
% 3.36/1.60  tff(c_74, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_18, c_60])).
% 3.36/1.60  tff(c_242, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~r1_tarski(k2_relat_1(C_81), B_83) | ~r1_tarski(k1_relat_1(C_81), A_82) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.36/1.60  tff(c_177, plain, (![A_70, B_71, C_72, D_73]: (k5_relset_1(A_70, B_71, C_72, D_73)=k7_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.60  tff(c_188, plain, (![D_73]: (k5_relset_1('#skF_2', '#skF_4', '#skF_5', D_73)=k7_relat_1('#skF_5', D_73))), inference(resolution, [status(thm)], [c_30, c_177])).
% 3.36/1.60  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.60  tff(c_195, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_28])).
% 3.36/1.60  tff(c_260, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_242, c_195])).
% 3.36/1.60  tff(c_312, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_260])).
% 3.36/1.60  tff(c_315, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_312])).
% 3.36/1.60  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_315])).
% 3.36/1.60  tff(c_320, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_260])).
% 3.36/1.60  tff(c_323, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_320])).
% 3.36/1.60  tff(c_1197, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_1172, c_323])).
% 3.36/1.60  tff(c_1202, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_510, c_1197])).
% 3.36/1.60  tff(c_1205, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_1202])).
% 3.36/1.60  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_1205])).
% 3.36/1.60  tff(c_1210, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_320])).
% 3.36/1.60  tff(c_1214, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_1210])).
% 3.36/1.60  tff(c_1218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_1214])).
% 3.36/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.60  
% 3.36/1.60  Inference rules
% 3.36/1.60  ----------------------
% 3.36/1.60  #Ref     : 0
% 3.36/1.60  #Sup     : 254
% 3.36/1.60  #Fact    : 0
% 3.36/1.60  #Define  : 0
% 3.36/1.60  #Split   : 5
% 3.36/1.60  #Chain   : 0
% 3.36/1.60  #Close   : 0
% 3.36/1.60  
% 3.36/1.60  Ordering : KBO
% 3.36/1.60  
% 3.36/1.60  Simplification rules
% 3.36/1.60  ----------------------
% 3.36/1.60  #Subsume      : 29
% 3.36/1.60  #Demod        : 76
% 3.36/1.60  #Tautology    : 60
% 3.36/1.60  #SimpNegUnit  : 0
% 3.36/1.60  #BackRed      : 4
% 3.36/1.60  
% 3.36/1.60  #Partial instantiations: 0
% 3.36/1.60  #Strategies tried      : 1
% 3.36/1.60  
% 3.36/1.60  Timing (in seconds)
% 3.36/1.60  ----------------------
% 3.36/1.60  Preprocessing        : 0.31
% 3.36/1.60  Parsing              : 0.17
% 3.36/1.60  CNF conversion       : 0.02
% 3.36/1.60  Main loop            : 0.50
% 3.36/1.60  Inferencing          : 0.20
% 3.36/1.60  Reduction            : 0.15
% 3.36/1.60  Demodulation         : 0.10
% 3.36/1.60  BG Simplification    : 0.02
% 3.36/1.60  Subsumption          : 0.10
% 3.36/1.60  Abstraction          : 0.03
% 3.36/1.60  MUC search           : 0.00
% 3.36/1.60  Cooper               : 0.00
% 3.36/1.60  Total                : 0.85
% 3.36/1.60  Index Insertion      : 0.00
% 3.36/1.60  Index Deletion       : 0.00
% 3.36/1.60  Index Matching       : 0.00
% 3.36/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
