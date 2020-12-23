%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:09 EST 2020

% Result     : Theorem 15.19s
% Output     : CNFRefutation 15.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 151 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 327 expanded)
%              Number of equality atoms :    6 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_26,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12522,plain,(
    ! [A_653,B_654,C_655] :
      ( k2_relset_1(A_653,B_654,C_655) = k2_relat_1(C_655)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_653,B_654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12526,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_12522])).

tff(c_42,plain,
    ( m1_subset_1('#skF_9','#skF_6')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_12551,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12526,c_44])).

tff(c_12527,plain,(
    ! [A_656,C_657] :
      ( r2_hidden(k4_tarski('#skF_4'(A_656,k2_relat_1(A_656),C_657),C_657),A_656)
      | ~ r2_hidden(C_657,k2_relat_1(A_656)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28105,plain,(
    ! [A_1407,C_1408,A_1409] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1407,k2_relat_1(A_1407),C_1408),C_1408),A_1409)
      | ~ m1_subset_1(A_1407,k1_zfmisc_1(A_1409))
      | ~ r2_hidden(C_1408,k2_relat_1(A_1407)) ) ),
    inference(resolution,[status(thm)],[c_12527,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38912,plain,(
    ! [A_1872,C_1873,C_1874,D_1875] :
      ( r2_hidden('#skF_4'(A_1872,k2_relat_1(A_1872),C_1873),C_1874)
      | ~ m1_subset_1(A_1872,k1_zfmisc_1(k2_zfmisc_1(C_1874,D_1875)))
      | ~ r2_hidden(C_1873,k2_relat_1(A_1872)) ) ),
    inference(resolution,[status(thm)],[c_28105,c_6])).

tff(c_38948,plain,(
    ! [C_1876] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1876),'#skF_6')
      | ~ r2_hidden(C_1876,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26,c_38912])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38971,plain,(
    ! [C_1877] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1877),'#skF_6')
      | ~ r2_hidden(C_1877,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_38948,c_10])).

tff(c_12,plain,(
    ! [A_11,C_26] :
      ( r2_hidden(k4_tarski('#skF_4'(A_11,k2_relat_1(A_11),C_26),C_26),A_11)
      | ~ r2_hidden(C_26,k2_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_13714,plain,(
    ! [A_792,C_793,A_794] :
      ( r2_hidden(k4_tarski('#skF_4'(A_792,k2_relat_1(A_792),C_793),C_793),A_794)
      | ~ m1_subset_1(A_792,k1_zfmisc_1(A_794))
      | ~ r2_hidden(C_793,k2_relat_1(A_792)) ) ),
    inference(resolution,[status(thm)],[c_12527,c_8])).

tff(c_26777,plain,(
    ! [A_1261,C_1262,C_1263,D_1264] :
      ( r2_hidden('#skF_4'(A_1261,k2_relat_1(A_1261),C_1262),C_1263)
      | ~ m1_subset_1(A_1261,k1_zfmisc_1(k2_zfmisc_1(C_1263,D_1264)))
      | ~ r2_hidden(C_1262,k2_relat_1(A_1261)) ) ),
    inference(resolution,[status(thm)],[c_13714,c_6])).

tff(c_26809,plain,(
    ! [C_1265] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1265),'#skF_6')
      | ~ r2_hidden(C_1265,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26,c_26777])).

tff(c_26853,plain,(
    ! [C_1266] :
      ( m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_1266),'#skF_6')
      | ~ r2_hidden(C_1266,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26809,c_10])).

tff(c_34,plain,(
    ! [E_74] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12565,plain,(
    ! [E_658] :
      ( ~ r2_hidden(k4_tarski(E_658,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_658,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_12569,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_12565])).

tff(c_12572,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_12569])).

tff(c_26860,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26853,c_12572])).

tff(c_26867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_26860])).

tff(c_26868,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_14,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26878,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_26868,c_14])).

tff(c_32,plain,(
    ! [E_74] :
      ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26880,plain,(
    ! [E_74] :
      ( ~ r2_hidden('#skF_8',k2_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(E_74,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12526,c_32])).

tff(c_26881,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_26880])).

tff(c_26890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26878,c_26881])).

tff(c_26921,plain,(
    ! [E_1271] :
      ( ~ r2_hidden(k4_tarski(E_1271,'#skF_10'),'#skF_7')
      | ~ m1_subset_1(E_1271,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_26880])).

tff(c_26925,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6')
    | ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_26921])).

tff(c_26928,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_26925])).

tff(c_38978,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_38971,c_26928])).

tff(c_38985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12551,c_38978])).

tff(c_38987,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7')
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38988,plain,(
    r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38987,c_38988])).

tff(c_38990,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38996,plain,(
    ! [C_1878,A_1879,D_1880] :
      ( r2_hidden(C_1878,k2_relat_1(A_1879))
      | ~ r2_hidden(k4_tarski(D_1880,C_1878),A_1879) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39000,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_38990,c_38996])).

tff(c_39079,plain,(
    ! [A_1902,B_1903,C_1904] :
      ( k2_relset_1(A_1902,B_1903,C_1904) = k2_relat_1(C_1904)
      | ~ m1_subset_1(C_1904,k1_zfmisc_1(k2_zfmisc_1(A_1902,B_1903))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39088,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_39079])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7'))
    | r2_hidden('#skF_10',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_39058,plain,(
    ~ r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_38987,c_38])).

tff(c_39089,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39088,c_39058])).

tff(c_39093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39000,c_39089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.19/6.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.19/6.81  
% 15.19/6.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.19/6.81  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 15.19/6.81  
% 15.19/6.81  %Foreground sorts:
% 15.19/6.81  
% 15.19/6.81  
% 15.19/6.81  %Background operators:
% 15.19/6.81  
% 15.19/6.81  
% 15.19/6.81  %Foreground operators:
% 15.19/6.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.19/6.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.19/6.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.19/6.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.19/6.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.19/6.81  tff('#skF_7', type, '#skF_7': $i).
% 15.19/6.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.19/6.81  tff('#skF_10', type, '#skF_10': $i).
% 15.19/6.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.19/6.81  tff('#skF_5', type, '#skF_5': $i).
% 15.19/6.81  tff('#skF_6', type, '#skF_6': $i).
% 15.19/6.81  tff('#skF_9', type, '#skF_9': $i).
% 15.19/6.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.19/6.81  tff('#skF_8', type, '#skF_8': $i).
% 15.19/6.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.19/6.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.19/6.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.19/6.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.19/6.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.19/6.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.19/6.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.19/6.81  
% 15.19/6.82  tff(f_73, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 15.19/6.82  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.19/6.82  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 15.19/6.82  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.19/6.82  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 15.19/6.82  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 15.19/6.82  tff(c_26, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_12522, plain, (![A_653, B_654, C_655]: (k2_relset_1(A_653, B_654, C_655)=k2_relat_1(C_655) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_653, B_654))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.19/6.82  tff(c_12526, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_12522])).
% 15.19/6.82  tff(c_42, plain, (m1_subset_1('#skF_9', '#skF_6') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_44, plain, (r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_42])).
% 15.19/6.82  tff(c_12551, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12526, c_44])).
% 15.19/6.82  tff(c_12527, plain, (![A_656, C_657]: (r2_hidden(k4_tarski('#skF_4'(A_656, k2_relat_1(A_656), C_657), C_657), A_656) | ~r2_hidden(C_657, k2_relat_1(A_656)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.19/6.82  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.19/6.82  tff(c_28105, plain, (![A_1407, C_1408, A_1409]: (r2_hidden(k4_tarski('#skF_4'(A_1407, k2_relat_1(A_1407), C_1408), C_1408), A_1409) | ~m1_subset_1(A_1407, k1_zfmisc_1(A_1409)) | ~r2_hidden(C_1408, k2_relat_1(A_1407)))), inference(resolution, [status(thm)], [c_12527, c_8])).
% 15.19/6.82  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.19/6.82  tff(c_38912, plain, (![A_1872, C_1873, C_1874, D_1875]: (r2_hidden('#skF_4'(A_1872, k2_relat_1(A_1872), C_1873), C_1874) | ~m1_subset_1(A_1872, k1_zfmisc_1(k2_zfmisc_1(C_1874, D_1875))) | ~r2_hidden(C_1873, k2_relat_1(A_1872)))), inference(resolution, [status(thm)], [c_28105, c_6])).
% 15.19/6.82  tff(c_38948, plain, (![C_1876]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1876), '#skF_6') | ~r2_hidden(C_1876, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_26, c_38912])).
% 15.19/6.82  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.19/6.82  tff(c_38971, plain, (![C_1877]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1877), '#skF_6') | ~r2_hidden(C_1877, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_38948, c_10])).
% 15.19/6.82  tff(c_12, plain, (![A_11, C_26]: (r2_hidden(k4_tarski('#skF_4'(A_11, k2_relat_1(A_11), C_26), C_26), A_11) | ~r2_hidden(C_26, k2_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.19/6.82  tff(c_13714, plain, (![A_792, C_793, A_794]: (r2_hidden(k4_tarski('#skF_4'(A_792, k2_relat_1(A_792), C_793), C_793), A_794) | ~m1_subset_1(A_792, k1_zfmisc_1(A_794)) | ~r2_hidden(C_793, k2_relat_1(A_792)))), inference(resolution, [status(thm)], [c_12527, c_8])).
% 15.19/6.82  tff(c_26777, plain, (![A_1261, C_1262, C_1263, D_1264]: (r2_hidden('#skF_4'(A_1261, k2_relat_1(A_1261), C_1262), C_1263) | ~m1_subset_1(A_1261, k1_zfmisc_1(k2_zfmisc_1(C_1263, D_1264))) | ~r2_hidden(C_1262, k2_relat_1(A_1261)))), inference(resolution, [status(thm)], [c_13714, c_6])).
% 15.19/6.82  tff(c_26809, plain, (![C_1265]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1265), '#skF_6') | ~r2_hidden(C_1265, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_26, c_26777])).
% 15.19/6.82  tff(c_26853, plain, (![C_1266]: (m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_1266), '#skF_6') | ~r2_hidden(C_1266, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_26809, c_10])).
% 15.19/6.82  tff(c_34, plain, (![E_74]: (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_12565, plain, (![E_658]: (~r2_hidden(k4_tarski(E_658, '#skF_10'), '#skF_7') | ~m1_subset_1(E_658, '#skF_6'))), inference(splitLeft, [status(thm)], [c_34])).
% 15.19/6.82  tff(c_12569, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_12565])).
% 15.19/6.82  tff(c_12572, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12551, c_12569])).
% 15.19/6.82  tff(c_26860, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_26853, c_12572])).
% 15.19/6.82  tff(c_26867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12551, c_26860])).
% 15.19/6.82  tff(c_26868, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_34])).
% 15.19/6.82  tff(c_14, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.19/6.82  tff(c_26878, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_26868, c_14])).
% 15.19/6.82  tff(c_32, plain, (![E_74]: (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_26880, plain, (![E_74]: (~r2_hidden('#skF_8', k2_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(E_74, '#skF_10'), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12526, c_32])).
% 15.19/6.82  tff(c_26881, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_26880])).
% 15.19/6.82  tff(c_26890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26878, c_26881])).
% 15.19/6.82  tff(c_26921, plain, (![E_1271]: (~r2_hidden(k4_tarski(E_1271, '#skF_10'), '#skF_7') | ~m1_subset_1(E_1271, '#skF_6'))), inference(splitRight, [status(thm)], [c_26880])).
% 15.19/6.82  tff(c_26925, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6') | ~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_26921])).
% 15.19/6.82  tff(c_26928, plain, (~m1_subset_1('#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12551, c_26925])).
% 15.19/6.82  tff(c_38978, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_38971, c_26928])).
% 15.19/6.82  tff(c_38985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12551, c_38978])).
% 15.19/6.82  tff(c_38987, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 15.19/6.82  tff(c_40, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7') | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_38988, plain, (r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 15.19/6.82  tff(c_38989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38987, c_38988])).
% 15.19/6.82  tff(c_38990, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 15.19/6.82  tff(c_38996, plain, (![C_1878, A_1879, D_1880]: (r2_hidden(C_1878, k2_relat_1(A_1879)) | ~r2_hidden(k4_tarski(D_1880, C_1878), A_1879))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.19/6.82  tff(c_39000, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_38990, c_38996])).
% 15.19/6.82  tff(c_39079, plain, (![A_1902, B_1903, C_1904]: (k2_relset_1(A_1902, B_1903, C_1904)=k2_relat_1(C_1904) | ~m1_subset_1(C_1904, k1_zfmisc_1(k2_zfmisc_1(A_1902, B_1903))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.19/6.82  tff(c_39088, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_39079])).
% 15.19/6.82  tff(c_38, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7')) | r2_hidden('#skF_10', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.19/6.82  tff(c_39058, plain, (~r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_38987, c_38])).
% 15.19/6.82  tff(c_39089, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_39088, c_39058])).
% 15.19/6.82  tff(c_39093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39000, c_39089])).
% 15.19/6.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.19/6.82  
% 15.19/6.82  Inference rules
% 15.19/6.82  ----------------------
% 15.19/6.82  #Ref     : 0
% 15.19/6.82  #Sup     : 10356
% 15.19/6.82  #Fact    : 6
% 15.19/6.82  #Define  : 0
% 15.19/6.82  #Split   : 37
% 15.19/6.82  #Chain   : 0
% 15.19/6.82  #Close   : 0
% 15.19/6.82  
% 15.19/6.82  Ordering : KBO
% 15.19/6.83  
% 15.19/6.83  Simplification rules
% 15.19/6.83  ----------------------
% 15.19/6.83  #Subsume      : 831
% 15.19/6.83  #Demod        : 293
% 15.19/6.83  #Tautology    : 233
% 15.19/6.83  #SimpNegUnit  : 70
% 15.19/6.83  #BackRed      : 152
% 15.19/6.83  
% 15.19/6.83  #Partial instantiations: 0
% 15.19/6.83  #Strategies tried      : 1
% 15.19/6.83  
% 15.19/6.83  Timing (in seconds)
% 15.19/6.83  ----------------------
% 15.19/6.83  Preprocessing        : 0.32
% 15.19/6.83  Parsing              : 0.16
% 15.19/6.83  CNF conversion       : 0.03
% 15.19/6.83  Main loop            : 5.73
% 15.19/6.83  Inferencing          : 1.30
% 15.19/6.83  Reduction            : 1.23
% 15.19/6.83  Demodulation         : 0.79
% 15.19/6.83  BG Simplification    : 0.21
% 15.19/6.83  Subsumption          : 2.45
% 15.19/6.83  Abstraction          : 0.26
% 15.19/6.83  MUC search           : 0.00
% 15.19/6.83  Cooper               : 0.00
% 15.19/6.83  Total                : 6.08
% 15.19/6.83  Index Insertion      : 0.00
% 15.19/6.83  Index Deletion       : 0.00
% 15.19/6.83  Index Matching       : 0.00
% 15.19/6.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
