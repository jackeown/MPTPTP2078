%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 164 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 330 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_48,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(A_75,C_76)
      | ~ r1_tarski(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_13')
      | ~ r1_tarski(A_75,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_50,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_11')
      | ~ r1_tarski(A_75,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_52,plain,(
    m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_52,c_53])).

tff(c_858,plain,(
    ! [C_181,A_182,B_183] :
      ( m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ r1_tarski(k2_relat_1(C_181),B_183)
      | ~ r1_tarski(k1_relat_1(C_181),A_182)
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ~ m1_subset_1('#skF_14',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_13'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_867,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_14'),'#skF_13')
    | ~ r1_tarski(k1_relat_1('#skF_14'),'#skF_11')
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_858,c_46])).

tff(c_872,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_14'),'#skF_13')
    | ~ r1_tarski(k1_relat_1('#skF_14'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_867])).

tff(c_873,plain,(
    ~ r1_tarski(k1_relat_1('#skF_14'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_872])).

tff(c_881,plain,(
    ~ r1_tarski(k1_relat_1('#skF_14'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_873])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [A_101,B_102,A_103] :
      ( r2_hidden('#skF_1'(A_101,B_102),A_103)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(A_103))
      | r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_104,A_105] :
      ( ~ m1_subset_1(A_104,k1_zfmisc_1(A_105))
      | r1_tarski(A_104,A_105) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_160,plain,(
    r1_tarski('#skF_14',k2_zfmisc_1('#skF_10','#skF_12')) ),
    inference(resolution,[status(thm)],[c_52,c_156])).

tff(c_208,plain,(
    ! [C_111,A_112] :
      ( r2_hidden(k4_tarski(C_111,'#skF_5'(A_112,k1_relat_1(A_112),C_111)),A_112)
      | ~ r2_hidden(C_111,k1_relat_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2272,plain,(
    ! [C_279,A_280,B_281] :
      ( r2_hidden(k4_tarski(C_279,'#skF_5'(A_280,k1_relat_1(A_280),C_279)),B_281)
      | ~ r1_tarski(A_280,B_281)
      | ~ r2_hidden(C_279,k1_relat_1(A_280)) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_20,plain,(
    ! [C_32,A_17,D_35] :
      ( r2_hidden(C_32,k1_relat_1(A_17))
      | ~ r2_hidden(k4_tarski(C_32,D_35),A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2424,plain,(
    ! [C_288,B_289,A_290] :
      ( r2_hidden(C_288,k1_relat_1(B_289))
      | ~ r1_tarski(A_290,B_289)
      | ~ r2_hidden(C_288,k1_relat_1(A_290)) ) ),
    inference(resolution,[status(thm)],[c_2272,c_20])).

tff(c_2644,plain,(
    ! [C_293] :
      ( r2_hidden(C_293,k1_relat_1(k2_zfmisc_1('#skF_10','#skF_12')))
      | ~ r2_hidden(C_293,k1_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_160,c_2424])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10,D_12] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,(
    ! [C_111,C_11,D_12] :
      ( r2_hidden(C_111,C_11)
      | ~ r2_hidden(C_111,k1_relat_1(k2_zfmisc_1(C_11,D_12))) ) ),
    inference(resolution,[status(thm)],[c_208,c_14])).

tff(c_2717,plain,(
    ! [C_294] :
      ( r2_hidden(C_294,'#skF_10')
      | ~ r2_hidden(C_294,k1_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_2644,c_228])).

tff(c_2794,plain,(
    ! [B_295] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_14'),B_295),'#skF_10')
      | r1_tarski(k1_relat_1('#skF_14'),B_295) ) ),
    inference(resolution,[status(thm)],[c_6,c_2717])).

tff(c_2808,plain,(
    r1_tarski(k1_relat_1('#skF_14'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_2794,c_4])).

tff(c_2817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_881,c_881,c_2808])).

tff(c_2818,plain,(
    ~ r1_tarski(k2_relat_1('#skF_14'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_2826,plain,(
    ~ r1_tarski(k2_relat_1('#skF_14'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_79,c_2818])).

tff(c_254,plain,(
    ! [A_116,C_117] :
      ( r2_hidden(k4_tarski('#skF_9'(A_116,k2_relat_1(A_116),C_117),C_117),A_116)
      | ~ r2_hidden(C_117,k2_relat_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4098,plain,(
    ! [A_377,C_378,B_379] :
      ( r2_hidden(k4_tarski('#skF_9'(A_377,k2_relat_1(A_377),C_378),C_378),B_379)
      | ~ r1_tarski(A_377,B_379)
      | ~ r2_hidden(C_378,k2_relat_1(A_377)) ) ),
    inference(resolution,[status(thm)],[c_254,c_2])).

tff(c_32,plain,(
    ! [C_51,A_36,D_54] :
      ( r2_hidden(C_51,k2_relat_1(A_36))
      | ~ r2_hidden(k4_tarski(D_54,C_51),A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4163,plain,(
    ! [C_380,B_381,A_382] :
      ( r2_hidden(C_380,k2_relat_1(B_381))
      | ~ r1_tarski(A_382,B_381)
      | ~ r2_hidden(C_380,k2_relat_1(A_382)) ) ),
    inference(resolution,[status(thm)],[c_4098,c_32])).

tff(c_4350,plain,(
    ! [C_385] :
      ( r2_hidden(C_385,k2_relat_1(k2_zfmisc_1('#skF_10','#skF_12')))
      | ~ r2_hidden(C_385,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_160,c_4163])).

tff(c_12,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_278,plain,(
    ! [C_117,D_12,C_11] :
      ( r2_hidden(C_117,D_12)
      | ~ r2_hidden(C_117,k2_relat_1(k2_zfmisc_1(C_11,D_12))) ) ),
    inference(resolution,[status(thm)],[c_254,c_12])).

tff(c_4414,plain,(
    ! [C_386] :
      ( r2_hidden(C_386,'#skF_12')
      | ~ r2_hidden(C_386,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_4350,c_278])).

tff(c_4567,plain,(
    ! [B_388] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_14'),B_388),'#skF_12')
      | r1_tarski(k2_relat_1('#skF_14'),B_388) ) ),
    inference(resolution,[status(thm)],[c_6,c_4414])).

tff(c_4579,plain,(
    r1_tarski(k2_relat_1('#skF_14'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_4567,c_4])).

tff(c_4587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2826,c_2826,c_4579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.18  
% 5.68/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_14 > #skF_13 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 5.68/2.18  
% 5.68/2.18  %Foreground sorts:
% 5.68/2.18  
% 5.68/2.18  
% 5.68/2.18  %Background operators:
% 5.68/2.18  
% 5.68/2.18  
% 5.68/2.18  %Foreground operators:
% 5.68/2.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.68/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.68/2.18  tff('#skF_11', type, '#skF_11': $i).
% 5.68/2.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.68/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.68/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.68/2.18  tff('#skF_10', type, '#skF_10': $i).
% 5.68/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.68/2.18  tff('#skF_14', type, '#skF_14': $i).
% 5.68/2.18  tff('#skF_13', type, '#skF_13': $i).
% 5.68/2.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.68/2.18  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.68/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.18  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 5.68/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.68/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.68/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.68/2.18  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.68/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.68/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.68/2.18  tff('#skF_12', type, '#skF_12': $i).
% 5.68/2.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.68/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.18  
% 5.68/2.20  tff(f_88, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 5.68/2.20  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.68/2.20  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.68/2.20  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.68/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.68/2.20  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.68/2.20  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.68/2.20  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.68/2.20  tff(f_67, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 5.68/2.20  tff(c_48, plain, (r1_tarski('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.20  tff(c_71, plain, (![A_75, C_76, B_77]: (r1_tarski(A_75, C_76) | ~r1_tarski(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.68/2.20  tff(c_79, plain, (![A_75]: (r1_tarski(A_75, '#skF_13') | ~r1_tarski(A_75, '#skF_12'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 5.68/2.20  tff(c_50, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.20  tff(c_80, plain, (![A_75]: (r1_tarski(A_75, '#skF_11') | ~r1_tarski(A_75, '#skF_10'))), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.68/2.20  tff(c_52, plain, (m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_12')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.20  tff(c_53, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.68/2.20  tff(c_57, plain, (v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_52, c_53])).
% 5.68/2.20  tff(c_858, plain, (![C_181, A_182, B_183]: (m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~r1_tarski(k2_relat_1(C_181), B_183) | ~r1_tarski(k1_relat_1(C_181), A_182) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.68/2.20  tff(c_46, plain, (~m1_subset_1('#skF_14', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_13')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.20  tff(c_867, plain, (~r1_tarski(k2_relat_1('#skF_14'), '#skF_13') | ~r1_tarski(k1_relat_1('#skF_14'), '#skF_11') | ~v1_relat_1('#skF_14')), inference(resolution, [status(thm)], [c_858, c_46])).
% 5.68/2.20  tff(c_872, plain, (~r1_tarski(k2_relat_1('#skF_14'), '#skF_13') | ~r1_tarski(k1_relat_1('#skF_14'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_867])).
% 5.68/2.20  tff(c_873, plain, (~r1_tarski(k1_relat_1('#skF_14'), '#skF_11')), inference(splitLeft, [status(thm)], [c_872])).
% 5.68/2.20  tff(c_881, plain, (~r1_tarski(k1_relat_1('#skF_14'), '#skF_10')), inference(resolution, [status(thm)], [c_80, c_873])).
% 5.68/2.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.20  tff(c_90, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.68/2.20  tff(c_144, plain, (![A_101, B_102, A_103]: (r2_hidden('#skF_1'(A_101, B_102), A_103) | ~m1_subset_1(A_101, k1_zfmisc_1(A_103)) | r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_6, c_90])).
% 5.68/2.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.20  tff(c_156, plain, (![A_104, A_105]: (~m1_subset_1(A_104, k1_zfmisc_1(A_105)) | r1_tarski(A_104, A_105))), inference(resolution, [status(thm)], [c_144, c_4])).
% 5.68/2.20  tff(c_160, plain, (r1_tarski('#skF_14', k2_zfmisc_1('#skF_10', '#skF_12'))), inference(resolution, [status(thm)], [c_52, c_156])).
% 5.68/2.20  tff(c_208, plain, (![C_111, A_112]: (r2_hidden(k4_tarski(C_111, '#skF_5'(A_112, k1_relat_1(A_112), C_111)), A_112) | ~r2_hidden(C_111, k1_relat_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.68/2.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.20  tff(c_2272, plain, (![C_279, A_280, B_281]: (r2_hidden(k4_tarski(C_279, '#skF_5'(A_280, k1_relat_1(A_280), C_279)), B_281) | ~r1_tarski(A_280, B_281) | ~r2_hidden(C_279, k1_relat_1(A_280)))), inference(resolution, [status(thm)], [c_208, c_2])).
% 5.68/2.20  tff(c_20, plain, (![C_32, A_17, D_35]: (r2_hidden(C_32, k1_relat_1(A_17)) | ~r2_hidden(k4_tarski(C_32, D_35), A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.68/2.20  tff(c_2424, plain, (![C_288, B_289, A_290]: (r2_hidden(C_288, k1_relat_1(B_289)) | ~r1_tarski(A_290, B_289) | ~r2_hidden(C_288, k1_relat_1(A_290)))), inference(resolution, [status(thm)], [c_2272, c_20])).
% 5.68/2.20  tff(c_2644, plain, (![C_293]: (r2_hidden(C_293, k1_relat_1(k2_zfmisc_1('#skF_10', '#skF_12'))) | ~r2_hidden(C_293, k1_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_160, c_2424])).
% 5.68/2.20  tff(c_14, plain, (![A_9, C_11, B_10, D_12]: (r2_hidden(A_9, C_11) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.20  tff(c_228, plain, (![C_111, C_11, D_12]: (r2_hidden(C_111, C_11) | ~r2_hidden(C_111, k1_relat_1(k2_zfmisc_1(C_11, D_12))))), inference(resolution, [status(thm)], [c_208, c_14])).
% 5.68/2.20  tff(c_2717, plain, (![C_294]: (r2_hidden(C_294, '#skF_10') | ~r2_hidden(C_294, k1_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_2644, c_228])).
% 5.68/2.20  tff(c_2794, plain, (![B_295]: (r2_hidden('#skF_1'(k1_relat_1('#skF_14'), B_295), '#skF_10') | r1_tarski(k1_relat_1('#skF_14'), B_295))), inference(resolution, [status(thm)], [c_6, c_2717])).
% 5.68/2.20  tff(c_2808, plain, (r1_tarski(k1_relat_1('#skF_14'), '#skF_10')), inference(resolution, [status(thm)], [c_2794, c_4])).
% 5.68/2.20  tff(c_2817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_881, c_881, c_2808])).
% 5.68/2.20  tff(c_2818, plain, (~r1_tarski(k2_relat_1('#skF_14'), '#skF_13')), inference(splitRight, [status(thm)], [c_872])).
% 5.68/2.20  tff(c_2826, plain, (~r1_tarski(k2_relat_1('#skF_14'), '#skF_12')), inference(resolution, [status(thm)], [c_79, c_2818])).
% 5.68/2.20  tff(c_254, plain, (![A_116, C_117]: (r2_hidden(k4_tarski('#skF_9'(A_116, k2_relat_1(A_116), C_117), C_117), A_116) | ~r2_hidden(C_117, k2_relat_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.68/2.20  tff(c_4098, plain, (![A_377, C_378, B_379]: (r2_hidden(k4_tarski('#skF_9'(A_377, k2_relat_1(A_377), C_378), C_378), B_379) | ~r1_tarski(A_377, B_379) | ~r2_hidden(C_378, k2_relat_1(A_377)))), inference(resolution, [status(thm)], [c_254, c_2])).
% 5.68/2.20  tff(c_32, plain, (![C_51, A_36, D_54]: (r2_hidden(C_51, k2_relat_1(A_36)) | ~r2_hidden(k4_tarski(D_54, C_51), A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.68/2.20  tff(c_4163, plain, (![C_380, B_381, A_382]: (r2_hidden(C_380, k2_relat_1(B_381)) | ~r1_tarski(A_382, B_381) | ~r2_hidden(C_380, k2_relat_1(A_382)))), inference(resolution, [status(thm)], [c_4098, c_32])).
% 5.68/2.20  tff(c_4350, plain, (![C_385]: (r2_hidden(C_385, k2_relat_1(k2_zfmisc_1('#skF_10', '#skF_12'))) | ~r2_hidden(C_385, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_160, c_4163])).
% 5.68/2.20  tff(c_12, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.20  tff(c_278, plain, (![C_117, D_12, C_11]: (r2_hidden(C_117, D_12) | ~r2_hidden(C_117, k2_relat_1(k2_zfmisc_1(C_11, D_12))))), inference(resolution, [status(thm)], [c_254, c_12])).
% 5.68/2.20  tff(c_4414, plain, (![C_386]: (r2_hidden(C_386, '#skF_12') | ~r2_hidden(C_386, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_4350, c_278])).
% 5.68/2.20  tff(c_4567, plain, (![B_388]: (r2_hidden('#skF_1'(k2_relat_1('#skF_14'), B_388), '#skF_12') | r1_tarski(k2_relat_1('#skF_14'), B_388))), inference(resolution, [status(thm)], [c_6, c_4414])).
% 5.68/2.20  tff(c_4579, plain, (r1_tarski(k2_relat_1('#skF_14'), '#skF_12')), inference(resolution, [status(thm)], [c_4567, c_4])).
% 5.68/2.20  tff(c_4587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2826, c_2826, c_4579])).
% 5.68/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.20  
% 5.68/2.20  Inference rules
% 5.68/2.20  ----------------------
% 5.68/2.20  #Ref     : 0
% 5.68/2.20  #Sup     : 1148
% 5.68/2.20  #Fact    : 0
% 5.68/2.20  #Define  : 0
% 5.68/2.20  #Split   : 9
% 5.68/2.20  #Chain   : 0
% 5.68/2.20  #Close   : 0
% 5.68/2.20  
% 5.68/2.20  Ordering : KBO
% 5.68/2.20  
% 5.68/2.20  Simplification rules
% 5.68/2.20  ----------------------
% 5.68/2.20  #Subsume      : 189
% 5.68/2.20  #Demod        : 15
% 5.68/2.20  #Tautology    : 34
% 5.68/2.20  #SimpNegUnit  : 2
% 5.68/2.20  #BackRed      : 0
% 5.68/2.20  
% 5.68/2.20  #Partial instantiations: 0
% 5.68/2.20  #Strategies tried      : 1
% 5.68/2.20  
% 5.68/2.20  Timing (in seconds)
% 5.68/2.20  ----------------------
% 5.68/2.20  Preprocessing        : 0.33
% 5.68/2.20  Parsing              : 0.18
% 5.68/2.20  CNF conversion       : 0.03
% 5.68/2.20  Main loop            : 1.05
% 5.68/2.20  Inferencing          : 0.33
% 5.68/2.20  Reduction            : 0.26
% 5.68/2.20  Demodulation         : 0.17
% 5.68/2.20  BG Simplification    : 0.04
% 5.68/2.20  Subsumption          : 0.33
% 5.68/2.20  Abstraction          : 0.05
% 5.68/2.20  MUC search           : 0.00
% 5.68/2.20  Cooper               : 0.00
% 5.68/2.20  Total                : 1.42
% 5.68/2.20  Index Insertion      : 0.00
% 5.68/2.20  Index Deletion       : 0.00
% 5.68/2.20  Index Matching       : 0.00
% 5.68/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
