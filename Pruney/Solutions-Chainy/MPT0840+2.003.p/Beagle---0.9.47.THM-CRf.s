%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 15.35s
% Output     : CNFRefutation 15.51s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 643 expanded)
%              Number of leaves         :   37 ( 231 expanded)
%              Depth                    :    9
%              Number of atoms          :  387 (2065 expanded)
%              Number of equality atoms :   16 (  88 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C)))
                       => ! [F,G] :
                            ( r2_hidden(k4_tarski(F,G),k4_relset_1(A,B,B,C,D,E))
                          <=> ? [H] :
                                ( m1_subset_1(H,B)
                                & r2_hidden(k4_tarski(F,H),D)
                                & r2_hidden(k4_tarski(H,G),E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_34,plain,(
    ! [A_115,B_116] : v1_relat_1(k2_zfmisc_1(A_115,B_116)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_65,plain,(
    ! [B_342,A_343] :
      ( v1_relat_1(B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_343))
      | ~ v1_relat_1(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_74,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_68])).

tff(c_38,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,
    ( v1_relat_1('#skF_11')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_77,plain,(
    v1_relat_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_32,plain,(
    ! [A_113,B_114] :
      ( v1_relat_1(k5_relat_1(A_113,B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20966,plain,(
    ! [F_2252,B_2256,D_2254,E_2255,A_2257,C_2253] :
      ( k4_relset_1(A_2257,B_2256,C_2253,D_2254,E_2255,F_2252) = k5_relat_1(E_2255,F_2252)
      | ~ m1_subset_1(F_2252,k1_zfmisc_1(k2_zfmisc_1(C_2253,D_2254)))
      | ~ m1_subset_1(E_2255,k1_zfmisc_1(k2_zfmisc_1(A_2257,B_2256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_21347,plain,(
    ! [A_2312,B_2313,E_2314] :
      ( k4_relset_1(A_2312,B_2313,'#skF_8','#skF_9',E_2314,'#skF_11') = k5_relat_1(E_2314,'#skF_11')
      | ~ m1_subset_1(E_2314,k1_zfmisc_1(k2_zfmisc_1(A_2312,B_2313))) ) ),
    inference(resolution,[status(thm)],[c_38,c_20966])).

tff(c_21364,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_21347])).

tff(c_62,plain,
    ( m1_subset_1('#skF_14','#skF_8')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_21370,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21364,c_78])).

tff(c_21391,plain,(
    ! [B_2317,F_2318,D_2315,A_2319,E_2316] :
      ( r2_hidden(k4_tarski(D_2315,E_2316),k5_relat_1(A_2319,B_2317))
      | ~ r2_hidden(k4_tarski(F_2318,E_2316),B_2317)
      | ~ r2_hidden(k4_tarski(D_2315,F_2318),A_2319)
      | ~ v1_relat_1(k5_relat_1(A_2319,B_2317))
      | ~ v1_relat_1(B_2317)
      | ~ v1_relat_1(A_2319) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21406,plain,(
    ! [D_2315,A_2319] :
      ( r2_hidden(k4_tarski(D_2315,'#skF_16'),k5_relat_1(A_2319,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_2315,'#skF_15'),A_2319)
      | ~ v1_relat_1(k5_relat_1(A_2319,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_2319) ) ),
    inference(resolution,[status(thm)],[c_21370,c_21391])).

tff(c_21864,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_21406])).

tff(c_21867,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_21864])).

tff(c_21871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_21867])).

tff(c_21873,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_21406])).

tff(c_30,plain,(
    ! [D_105,E_106,A_14,B_66] :
      ( r2_hidden(k4_tarski(D_105,'#skF_1'(D_105,E_106,k5_relat_1(A_14,B_66),B_66,A_14)),A_14)
      | ~ r2_hidden(k4_tarski(D_105,E_106),k5_relat_1(A_14,B_66))
      | ~ v1_relat_1(k5_relat_1(A_14,B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21514,plain,(
    ! [D_2335,E_2336,A_2337,B_2338] :
      ( r2_hidden(k4_tarski('#skF_1'(D_2335,E_2336,k5_relat_1(A_2337,B_2338),B_2338,A_2337),E_2336),B_2338)
      | ~ r2_hidden(k4_tarski(D_2335,E_2336),k5_relat_1(A_2337,B_2338))
      | ~ v1_relat_1(k5_relat_1(A_2337,B_2338))
      | ~ v1_relat_1(B_2338)
      | ~ v1_relat_1(A_2337) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17736,plain,(
    ! [D_1820,C_1819,B_1822,F_1818,E_1821,A_1823] :
      ( k4_relset_1(A_1823,B_1822,C_1819,D_1820,E_1821,F_1818) = k5_relat_1(E_1821,F_1818)
      | ~ m1_subset_1(F_1818,k1_zfmisc_1(k2_zfmisc_1(C_1819,D_1820)))
      | ~ m1_subset_1(E_1821,k1_zfmisc_1(k2_zfmisc_1(A_1823,B_1822))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17770,plain,(
    ! [A_1827,B_1828,E_1829] :
      ( k4_relset_1(A_1827,B_1828,'#skF_8','#skF_9',E_1829,'#skF_11') = k5_relat_1(E_1829,'#skF_11')
      | ~ m1_subset_1(E_1829,k1_zfmisc_1(k2_zfmisc_1(A_1827,B_1828))) ) ),
    inference(resolution,[status(thm)],[c_38,c_17736])).

tff(c_17782,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_17770])).

tff(c_17786,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17782,c_78])).

tff(c_26,plain,(
    ! [B_66,F_109,E_106,D_105,A_14] :
      ( r2_hidden(k4_tarski(D_105,E_106),k5_relat_1(A_14,B_66))
      | ~ r2_hidden(k4_tarski(F_109,E_106),B_66)
      | ~ r2_hidden(k4_tarski(D_105,F_109),A_14)
      | ~ v1_relat_1(k5_relat_1(A_14,B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17812,plain,(
    ! [D_105,A_14] :
      ( r2_hidden(k4_tarski(D_105,'#skF_16'),k5_relat_1(A_14,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_105,'#skF_15'),A_14)
      | ~ v1_relat_1(k5_relat_1(A_14,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_17786,c_26])).

tff(c_17900,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_17812])).

tff(c_17903,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_17900])).

tff(c_17907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_17903])).

tff(c_17909,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_17812])).

tff(c_17910,plain,(
    ! [D_1865,E_1866,A_1867,B_1868] :
      ( r2_hidden(k4_tarski('#skF_1'(D_1865,E_1866,k5_relat_1(A_1867,B_1868),B_1868,A_1867),E_1866),B_1868)
      | ~ r2_hidden(k4_tarski(D_1865,E_1866),k5_relat_1(A_1867,B_1868))
      | ~ v1_relat_1(k5_relat_1(A_1867,B_1868))
      | ~ v1_relat_1(B_1868)
      | ~ v1_relat_1(A_1867) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ! [H_337] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
      | ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_17686,plain,(
    ! [H_337] :
      ( ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_17919,plain,(
    ! [D_1865,A_1867] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_1865,'#skF_16',k5_relat_1(A_1867,'#skF_11'),'#skF_11',A_1867)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_1865,'#skF_16',k5_relat_1(A_1867,'#skF_11'),'#skF_11',A_1867),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1865,'#skF_16'),k5_relat_1(A_1867,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1867,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1867) ) ),
    inference(resolution,[status(thm)],[c_17910,c_17686])).

tff(c_17988,plain,(
    ! [D_1879,A_1880] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_1879,'#skF_16',k5_relat_1(A_1880,'#skF_11'),'#skF_11',A_1880)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_1879,'#skF_16',k5_relat_1(A_1880,'#skF_11'),'#skF_11',A_1880),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1879,'#skF_16'),k5_relat_1(A_1880,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1880,'#skF_11'))
      | ~ v1_relat_1(A_1880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_17919])).

tff(c_17992,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_17988])).

tff(c_17995,plain,(
    ~ m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_17909,c_17786,c_17992])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19046,plain,(
    ! [A_2067,B_2065,E_2069,D_2066,A_2068] :
      ( r2_hidden(k4_tarski('#skF_1'(D_2066,E_2069,k5_relat_1(A_2067,B_2065),B_2065,A_2067),E_2069),A_2068)
      | ~ m1_subset_1(B_2065,k1_zfmisc_1(A_2068))
      | ~ r2_hidden(k4_tarski(D_2066,E_2069),k5_relat_1(A_2067,B_2065))
      | ~ v1_relat_1(k5_relat_1(A_2067,B_2065))
      | ~ v1_relat_1(B_2065)
      | ~ v1_relat_1(A_2067) ) ),
    inference(resolution,[status(thm)],[c_17910,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20598,plain,(
    ! [A_2230,D_2228,D_2227,B_2229,E_2232,C_2231] :
      ( r2_hidden('#skF_1'(D_2227,E_2232,k5_relat_1(A_2230,B_2229),B_2229,A_2230),C_2231)
      | ~ m1_subset_1(B_2229,k1_zfmisc_1(k2_zfmisc_1(C_2231,D_2228)))
      | ~ r2_hidden(k4_tarski(D_2227,E_2232),k5_relat_1(A_2230,B_2229))
      | ~ v1_relat_1(k5_relat_1(A_2230,B_2229))
      | ~ v1_relat_1(B_2229)
      | ~ v1_relat_1(A_2230) ) ),
    inference(resolution,[status(thm)],[c_19046,c_6])).

tff(c_20620,plain,(
    ! [D_2227,E_2232,A_2230] :
      ( r2_hidden('#skF_1'(D_2227,E_2232,k5_relat_1(A_2230,'#skF_11'),'#skF_11',A_2230),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_2227,E_2232),k5_relat_1(A_2230,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_2230,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_2230) ) ),
    inference(resolution,[status(thm)],[c_38,c_20598])).

tff(c_20644,plain,(
    ! [D_2236,E_2237,A_2238] :
      ( r2_hidden('#skF_1'(D_2236,E_2237,k5_relat_1(A_2238,'#skF_11'),'#skF_11',A_2238),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_2236,E_2237),k5_relat_1(A_2238,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_2238,'#skF_11'))
      | ~ v1_relat_1(A_2238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_20620])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20854,plain,(
    ! [D_2245,E_2246,A_2247] :
      ( m1_subset_1('#skF_1'(D_2245,E_2246,k5_relat_1(A_2247,'#skF_11'),'#skF_11',A_2247),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_2245,E_2246),k5_relat_1(A_2247,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_2247,'#skF_11'))
      | ~ v1_relat_1(A_2247) ) ),
    inference(resolution,[status(thm)],[c_20644,c_10])).

tff(c_20900,plain,
    ( m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_17786,c_20854])).

tff(c_20923,plain,(
    m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_17909,c_20900])).

tff(c_20925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17995,c_20923])).

tff(c_20926,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9035,plain,(
    ! [E_1101,C_1099,B_1102,D_1100,A_1103,F_1098] :
      ( k4_relset_1(A_1103,B_1102,C_1099,D_1100,E_1101,F_1098) = k5_relat_1(E_1101,F_1098)
      | ~ m1_subset_1(F_1098,k1_zfmisc_1(k2_zfmisc_1(C_1099,D_1100)))
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9060,plain,(
    ! [A_1107,B_1108,E_1109] :
      ( k4_relset_1(A_1107,B_1108,'#skF_8','#skF_9',E_1109,'#skF_11') = k5_relat_1(E_1109,'#skF_11')
      | ~ m1_subset_1(E_1109,k1_zfmisc_1(k2_zfmisc_1(A_1107,B_1108))) ) ),
    inference(resolution,[status(thm)],[c_38,c_9035])).

tff(c_9067,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_9060])).

tff(c_9071,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9067,c_78])).

tff(c_9090,plain,(
    ! [E_1112,F_1114,A_1115,B_1113,D_1111] :
      ( r2_hidden(k4_tarski(D_1111,E_1112),k5_relat_1(A_1115,B_1113))
      | ~ r2_hidden(k4_tarski(F_1114,E_1112),B_1113)
      | ~ r2_hidden(k4_tarski(D_1111,F_1114),A_1115)
      | ~ v1_relat_1(k5_relat_1(A_1115,B_1113))
      | ~ v1_relat_1(B_1113)
      | ~ v1_relat_1(A_1115) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9095,plain,(
    ! [D_1111,A_1115] :
      ( r2_hidden(k4_tarski(D_1111,'#skF_16'),k5_relat_1(A_1115,k5_relat_1('#skF_10','#skF_11')))
      | ~ r2_hidden(k4_tarski(D_1111,'#skF_15'),A_1115)
      | ~ v1_relat_1(k5_relat_1(A_1115,k5_relat_1('#skF_10','#skF_11')))
      | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
      | ~ v1_relat_1(A_1115) ) ),
    inference(resolution,[status(thm)],[c_9071,c_9090])).

tff(c_9099,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_9095])).

tff(c_9102,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_9099])).

tff(c_9106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_9102])).

tff(c_9108,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_9095])).

tff(c_9122,plain,(
    ! [D_1123,E_1124,A_1125,B_1126] :
      ( r2_hidden(k4_tarski(D_1123,'#skF_1'(D_1123,E_1124,k5_relat_1(A_1125,B_1126),B_1126,A_1125)),A_1125)
      | ~ r2_hidden(k4_tarski(D_1123,E_1124),k5_relat_1(A_1125,B_1126))
      | ~ v1_relat_1(k5_relat_1(A_1125,B_1126))
      | ~ v1_relat_1(B_1126)
      | ~ v1_relat_1(A_1125) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9298,plain,(
    ! [D_1171,E_1170,A_1173,B_1172,A_1174] :
      ( r2_hidden(k4_tarski(D_1171,'#skF_1'(D_1171,E_1170,k5_relat_1(A_1174,B_1172),B_1172,A_1174)),A_1173)
      | ~ m1_subset_1(A_1174,k1_zfmisc_1(A_1173))
      | ~ r2_hidden(k4_tarski(D_1171,E_1170),k5_relat_1(A_1174,B_1172))
      | ~ v1_relat_1(k5_relat_1(A_1174,B_1172))
      | ~ v1_relat_1(B_1172)
      | ~ v1_relat_1(A_1174) ) ),
    inference(resolution,[status(thm)],[c_9122,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10665,plain,(
    ! [E_1358,B_1362,A_1357,D_1359,C_1361,D_1360] :
      ( r2_hidden('#skF_1'(D_1360,E_1358,k5_relat_1(A_1357,B_1362),B_1362,A_1357),D_1359)
      | ~ m1_subset_1(A_1357,k1_zfmisc_1(k2_zfmisc_1(C_1361,D_1359)))
      | ~ r2_hidden(k4_tarski(D_1360,E_1358),k5_relat_1(A_1357,B_1362))
      | ~ v1_relat_1(k5_relat_1(A_1357,B_1362))
      | ~ v1_relat_1(B_1362)
      | ~ v1_relat_1(A_1357) ) ),
    inference(resolution,[status(thm)],[c_9298,c_4])).

tff(c_10685,plain,(
    ! [D_1360,E_1358,B_1362] :
      ( r2_hidden('#skF_1'(D_1360,E_1358,k5_relat_1('#skF_10',B_1362),B_1362,'#skF_10'),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1360,E_1358),k5_relat_1('#skF_10',B_1362))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_1362))
      | ~ v1_relat_1(B_1362)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_40,c_10665])).

tff(c_10700,plain,(
    ! [D_1363,E_1364,B_1365] :
      ( r2_hidden('#skF_1'(D_1363,E_1364,k5_relat_1('#skF_10',B_1365),B_1365,'#skF_10'),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1363,E_1364),k5_relat_1('#skF_10',B_1365))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_1365))
      | ~ v1_relat_1(B_1365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10685])).

tff(c_10716,plain,(
    ! [D_1369,E_1370,B_1371] :
      ( m1_subset_1('#skF_1'(D_1369,E_1370,k5_relat_1('#skF_10',B_1371),B_1371,'#skF_10'),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1369,E_1370),k5_relat_1('#skF_10',B_1371))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_1371))
      | ~ v1_relat_1(B_1371) ) ),
    inference(resolution,[status(thm)],[c_10700,c_10])).

tff(c_10751,plain,
    ( m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_9071,c_10716])).

tff(c_10767,plain,(
    m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_9108,c_10751])).

tff(c_9160,plain,(
    ! [D_1132,E_1133,A_1134,B_1135] :
      ( r2_hidden(k4_tarski('#skF_1'(D_1132,E_1133,k5_relat_1(A_1134,B_1135),B_1135,A_1134),E_1133),B_1135)
      | ~ r2_hidden(k4_tarski(D_1132,E_1133),k5_relat_1(A_1134,B_1135))
      | ~ v1_relat_1(k5_relat_1(A_1134,B_1135))
      | ~ v1_relat_1(B_1135)
      | ~ v1_relat_1(A_1134) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    ! [H_337] :
      ( r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11')
      | ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9032,plain,(
    ! [H_337] :
      ( ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_9169,plain,(
    ! [D_1132,A_1134] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_1132,'#skF_16',k5_relat_1(A_1134,'#skF_11'),'#skF_11',A_1134)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_1132,'#skF_16',k5_relat_1(A_1134,'#skF_11'),'#skF_11',A_1134),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1132,'#skF_16'),k5_relat_1(A_1134,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1134,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1134) ) ),
    inference(resolution,[status(thm)],[c_9160,c_9032])).

tff(c_17644,plain,(
    ! [D_1804,A_1805] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_1804,'#skF_16',k5_relat_1(A_1805,'#skF_11'),'#skF_11',A_1805)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_1804,'#skF_16',k5_relat_1(A_1805,'#skF_11'),'#skF_11',A_1805),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1804,'#skF_16'),k5_relat_1(A_1805,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1805,'#skF_11'))
      | ~ v1_relat_1(A_1805) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_9169])).

tff(c_17652,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_17644])).

tff(c_17659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_9108,c_9071,c_10767,c_17652])).

tff(c_17660,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_21064,plain,(
    ! [B_2274,F_2275,D_2272,A_2276,E_2273] :
      ( r2_hidden(k4_tarski(D_2272,E_2273),k5_relat_1(A_2276,B_2274))
      | ~ r2_hidden(k4_tarski(F_2275,E_2273),B_2274)
      | ~ r2_hidden(k4_tarski(D_2272,F_2275),A_2276)
      | ~ v1_relat_1(k5_relat_1(A_2276,B_2274))
      | ~ v1_relat_1(B_2274)
      | ~ v1_relat_1(A_2276) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21074,plain,(
    ! [D_2272,A_2276] :
      ( r2_hidden(k4_tarski(D_2272,'#skF_13'),k5_relat_1(A_2276,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_2272,'#skF_14'),A_2276)
      | ~ v1_relat_1(k5_relat_1(A_2276,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_2276) ) ),
    inference(resolution,[status(thm)],[c_17660,c_21064])).

tff(c_21272,plain,(
    ! [D_2301,A_2302] :
      ( r2_hidden(k4_tarski(D_2301,'#skF_13'),k5_relat_1(A_2302,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_2301,'#skF_14'),A_2302)
      | ~ v1_relat_1(k5_relat_1(A_2302,'#skF_11'))
      | ~ v1_relat_1(A_2302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_21074])).

tff(c_21028,plain,(
    ! [A_2268,B_2269,E_2270] :
      ( k4_relset_1(A_2268,B_2269,'#skF_8','#skF_9',E_2270,'#skF_11') = k5_relat_1(E_2270,'#skF_11')
      | ~ m1_subset_1(E_2270,k1_zfmisc_1(k2_zfmisc_1(A_2268,B_2269))) ) ),
    inference(resolution,[status(thm)],[c_38,c_20966])).

tff(c_21045,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_21028])).

tff(c_48,plain,(
    ! [H_337] :
      ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
      | ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20985,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_21048,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21045,c_20985])).

tff(c_21277,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_21272,c_21048])).

tff(c_21286,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20926,c_21277])).

tff(c_21291,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_21286])).

tff(c_21295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_21291])).

tff(c_21296,plain,(
    ! [H_337] :
      ( ~ r2_hidden(k4_tarski(H_337,'#skF_16'),'#skF_11')
      | ~ r2_hidden(k4_tarski('#skF_15',H_337),'#skF_10')
      | ~ m1_subset_1(H_337,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_21519,plain,(
    ! [D_2335,A_2337] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_2335,'#skF_16',k5_relat_1(A_2337,'#skF_11'),'#skF_11',A_2337)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_2335,'#skF_16',k5_relat_1(A_2337,'#skF_11'),'#skF_11',A_2337),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_2335,'#skF_16'),k5_relat_1(A_2337,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_2337,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_2337) ) ),
    inference(resolution,[status(thm)],[c_21514,c_21296])).

tff(c_21936,plain,(
    ! [D_2416,A_2417] :
      ( ~ r2_hidden(k4_tarski('#skF_15','#skF_1'(D_2416,'#skF_16',k5_relat_1(A_2417,'#skF_11'),'#skF_11',A_2417)),'#skF_10')
      | ~ m1_subset_1('#skF_1'(D_2416,'#skF_16',k5_relat_1(A_2417,'#skF_11'),'#skF_11',A_2417),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_2416,'#skF_16'),k5_relat_1(A_2417,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_2417,'#skF_11'))
      | ~ v1_relat_1(A_2417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_21519])).

tff(c_21940,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_21936])).

tff(c_21943,plain,(
    ~ m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_21873,c_21370,c_21940])).

tff(c_22602,plain,(
    ! [B_2575,D_2579,E_2576,A_2578,A_2577] :
      ( r2_hidden(k4_tarski('#skF_1'(D_2579,E_2576,k5_relat_1(A_2577,B_2575),B_2575,A_2577),E_2576),A_2578)
      | ~ m1_subset_1(B_2575,k1_zfmisc_1(A_2578))
      | ~ r2_hidden(k4_tarski(D_2579,E_2576),k5_relat_1(A_2577,B_2575))
      | ~ v1_relat_1(k5_relat_1(A_2577,B_2575))
      | ~ v1_relat_1(B_2575)
      | ~ v1_relat_1(A_2577) ) ),
    inference(resolution,[status(thm)],[c_21514,c_8])).

tff(c_29142,plain,(
    ! [C_3081,D_3077,D_3078,E_3080,B_3082,A_3079] :
      ( r2_hidden('#skF_1'(D_3077,E_3080,k5_relat_1(A_3079,B_3082),B_3082,A_3079),C_3081)
      | ~ m1_subset_1(B_3082,k1_zfmisc_1(k2_zfmisc_1(C_3081,D_3078)))
      | ~ r2_hidden(k4_tarski(D_3077,E_3080),k5_relat_1(A_3079,B_3082))
      | ~ v1_relat_1(k5_relat_1(A_3079,B_3082))
      | ~ v1_relat_1(B_3082)
      | ~ v1_relat_1(A_3079) ) ),
    inference(resolution,[status(thm)],[c_22602,c_6])).

tff(c_29278,plain,(
    ! [D_3077,E_3080,A_3079] :
      ( r2_hidden('#skF_1'(D_3077,E_3080,k5_relat_1(A_3079,'#skF_11'),'#skF_11',A_3079),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_3077,E_3080),k5_relat_1(A_3079,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_3079,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_3079) ) ),
    inference(resolution,[status(thm)],[c_38,c_29142])).

tff(c_29337,plain,(
    ! [D_3086,E_3087,A_3088] :
      ( r2_hidden('#skF_1'(D_3086,E_3087,k5_relat_1(A_3088,'#skF_11'),'#skF_11',A_3088),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_3086,E_3087),k5_relat_1(A_3088,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_3088,'#skF_11'))
      | ~ v1_relat_1(A_3088) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_29278])).

tff(c_29509,plain,(
    ! [D_3092,E_3093,A_3094] :
      ( m1_subset_1('#skF_1'(D_3092,E_3093,k5_relat_1(A_3094,'#skF_11'),'#skF_11',A_3094),'#skF_8')
      | ~ r2_hidden(k4_tarski(D_3092,E_3093),k5_relat_1(A_3094,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_3094,'#skF_11'))
      | ~ v1_relat_1(A_3094) ) ),
    inference(resolution,[status(thm)],[c_29337,c_10])).

tff(c_29624,plain,
    ( m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_21370,c_29509])).

tff(c_29677,plain,(
    m1_subset_1('#skF_1'('#skF_15','#skF_16',k5_relat_1('#skF_10','#skF_11'),'#skF_11','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_21873,c_29624])).

tff(c_29679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21943,c_29677])).

tff(c_29681,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29686,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_29687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29681,c_29686])).

tff(c_29688,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_29689,plain,(
    ~ r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11')
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29767,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_13'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_29689,c_58])).

tff(c_29930,plain,(
    ! [B_3151,D_3149,A_3153,E_3150,F_3152] :
      ( r2_hidden(k4_tarski(D_3149,E_3150),k5_relat_1(A_3153,B_3151))
      | ~ r2_hidden(k4_tarski(F_3152,E_3150),B_3151)
      | ~ r2_hidden(k4_tarski(D_3149,F_3152),A_3153)
      | ~ v1_relat_1(k5_relat_1(A_3153,B_3151))
      | ~ v1_relat_1(B_3151)
      | ~ v1_relat_1(A_3153) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_29934,plain,(
    ! [D_3149,A_3153] :
      ( r2_hidden(k4_tarski(D_3149,'#skF_13'),k5_relat_1(A_3153,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_3149,'#skF_14'),A_3153)
      | ~ v1_relat_1(k5_relat_1(A_3153,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_3153) ) ),
    inference(resolution,[status(thm)],[c_29767,c_29930])).

tff(c_29993,plain,(
    ! [D_3167,A_3168] :
      ( r2_hidden(k4_tarski(D_3167,'#skF_13'),k5_relat_1(A_3168,'#skF_11'))
      | ~ r2_hidden(k4_tarski(D_3167,'#skF_14'),A_3168)
      | ~ v1_relat_1(k5_relat_1(A_3168,'#skF_11'))
      | ~ v1_relat_1(A_3168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_29934])).

tff(c_29858,plain,(
    ! [D_3139,E_3140,F_3137,B_3141,A_3142,C_3138] :
      ( k4_relset_1(A_3142,B_3141,C_3138,D_3139,E_3140,F_3137) = k5_relat_1(E_3140,F_3137)
      | ~ m1_subset_1(F_3137,k1_zfmisc_1(k2_zfmisc_1(C_3138,D_3139)))
      | ~ m1_subset_1(E_3140,k1_zfmisc_1(k2_zfmisc_1(A_3142,B_3141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_29900,plain,(
    ! [A_3146,B_3147,E_3148] :
      ( k4_relset_1(A_3146,B_3147,'#skF_8','#skF_9',E_3148,'#skF_11') = k5_relat_1(E_3148,'#skF_11')
      | ~ m1_subset_1(E_3148,k1_zfmisc_1(k2_zfmisc_1(A_3146,B_3147))) ) ),
    inference(resolution,[status(thm)],[c_38,c_29858])).

tff(c_29917,plain,(
    k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11') = k5_relat_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_29900])).

tff(c_56,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11'))
    | r2_hidden(k4_tarski('#skF_15','#skF_16'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29839,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k4_relset_1('#skF_7','#skF_8','#skF_8','#skF_9','#skF_10','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_29689,c_56])).

tff(c_29919,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29917,c_29839])).

tff(c_29998,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_14'),'#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_29993,c_29919])).

tff(c_30007,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_29688,c_29998])).

tff(c_30012,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_30007])).

tff(c_30016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_30012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.35/7.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/7.72  
% 15.35/7.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/7.72  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_15 > #skF_4 > #skF_7 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3 > #skF_12
% 15.35/7.72  
% 15.35/7.72  %Foreground sorts:
% 15.35/7.72  
% 15.35/7.72  
% 15.35/7.72  %Background operators:
% 15.35/7.72  
% 15.35/7.72  
% 15.35/7.72  %Foreground operators:
% 15.35/7.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.35/7.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.35/7.72  tff('#skF_11', type, '#skF_11': $i).
% 15.35/7.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_15', type, '#skF_15': $i).
% 15.35/7.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.35/7.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.35/7.72  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_7', type, '#skF_7': $i).
% 15.35/7.72  tff('#skF_10', type, '#skF_10': $i).
% 15.35/7.72  tff('#skF_16', type, '#skF_16': $i).
% 15.35/7.72  tff('#skF_14', type, '#skF_14': $i).
% 15.35/7.72  tff('#skF_13', type, '#skF_13': $i).
% 15.35/7.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_9', type, '#skF_9': $i).
% 15.35/7.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.35/7.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 15.35/7.72  tff('#skF_8', type, '#skF_8': $i).
% 15.35/7.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.35/7.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.35/7.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.35/7.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.35/7.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.35/7.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.35/7.72  tff('#skF_12', type, '#skF_12': $i).
% 15.35/7.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.35/7.72  
% 15.51/7.74  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.51/7.74  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (![F, G]: (r2_hidden(k4_tarski(F, G), k4_relset_1(A, B, B, C, D, E)) <=> (?[H]: ((m1_subset_1(H, B) & r2_hidden(k4_tarski(F, H), D)) & r2_hidden(k4_tarski(H, G), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_relset_1)).
% 15.51/7.74  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.51/7.74  tff(f_73, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 15.51/7.74  tff(f_81, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 15.51/7.74  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 15.51/7.74  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 15.51/7.74  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 15.51/7.74  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 15.51/7.74  tff(c_34, plain, (![A_115, B_116]: (v1_relat_1(k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.51/7.74  tff(c_40, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_65, plain, (![B_342, A_343]: (v1_relat_1(B_342) | ~m1_subset_1(B_342, k1_zfmisc_1(A_343)) | ~v1_relat_1(A_343))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.51/7.74  tff(c_68, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_65])).
% 15.51/7.74  tff(c_74, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_68])).
% 15.51/7.74  tff(c_38, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_71, plain, (v1_relat_1('#skF_11') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_38, c_65])).
% 15.51/7.74  tff(c_77, plain, (v1_relat_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71])).
% 15.51/7.74  tff(c_32, plain, (![A_113, B_114]: (v1_relat_1(k5_relat_1(A_113, B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.51/7.74  tff(c_20966, plain, (![F_2252, B_2256, D_2254, E_2255, A_2257, C_2253]: (k4_relset_1(A_2257, B_2256, C_2253, D_2254, E_2255, F_2252)=k5_relat_1(E_2255, F_2252) | ~m1_subset_1(F_2252, k1_zfmisc_1(k2_zfmisc_1(C_2253, D_2254))) | ~m1_subset_1(E_2255, k1_zfmisc_1(k2_zfmisc_1(A_2257, B_2256))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.51/7.74  tff(c_21347, plain, (![A_2312, B_2313, E_2314]: (k4_relset_1(A_2312, B_2313, '#skF_8', '#skF_9', E_2314, '#skF_11')=k5_relat_1(E_2314, '#skF_11') | ~m1_subset_1(E_2314, k1_zfmisc_1(k2_zfmisc_1(A_2312, B_2313))))), inference(resolution, [status(thm)], [c_38, c_20966])).
% 15.51/7.74  tff(c_21364, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_21347])).
% 15.51/7.74  tff(c_62, plain, (m1_subset_1('#skF_14', '#skF_8') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_62])).
% 15.51/7.74  tff(c_21370, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_21364, c_78])).
% 15.51/7.74  tff(c_21391, plain, (![B_2317, F_2318, D_2315, A_2319, E_2316]: (r2_hidden(k4_tarski(D_2315, E_2316), k5_relat_1(A_2319, B_2317)) | ~r2_hidden(k4_tarski(F_2318, E_2316), B_2317) | ~r2_hidden(k4_tarski(D_2315, F_2318), A_2319) | ~v1_relat_1(k5_relat_1(A_2319, B_2317)) | ~v1_relat_1(B_2317) | ~v1_relat_1(A_2319))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_21406, plain, (![D_2315, A_2319]: (r2_hidden(k4_tarski(D_2315, '#skF_16'), k5_relat_1(A_2319, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_2315, '#skF_15'), A_2319) | ~v1_relat_1(k5_relat_1(A_2319, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_2319))), inference(resolution, [status(thm)], [c_21370, c_21391])).
% 15.51/7.74  tff(c_21864, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_21406])).
% 15.51/7.74  tff(c_21867, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_21864])).
% 15.51/7.74  tff(c_21871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_21867])).
% 15.51/7.74  tff(c_21873, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_21406])).
% 15.51/7.74  tff(c_30, plain, (![D_105, E_106, A_14, B_66]: (r2_hidden(k4_tarski(D_105, '#skF_1'(D_105, E_106, k5_relat_1(A_14, B_66), B_66, A_14)), A_14) | ~r2_hidden(k4_tarski(D_105, E_106), k5_relat_1(A_14, B_66)) | ~v1_relat_1(k5_relat_1(A_14, B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_21514, plain, (![D_2335, E_2336, A_2337, B_2338]: (r2_hidden(k4_tarski('#skF_1'(D_2335, E_2336, k5_relat_1(A_2337, B_2338), B_2338, A_2337), E_2336), B_2338) | ~r2_hidden(k4_tarski(D_2335, E_2336), k5_relat_1(A_2337, B_2338)) | ~v1_relat_1(k5_relat_1(A_2337, B_2338)) | ~v1_relat_1(B_2338) | ~v1_relat_1(A_2337))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_17736, plain, (![D_1820, C_1819, B_1822, F_1818, E_1821, A_1823]: (k4_relset_1(A_1823, B_1822, C_1819, D_1820, E_1821, F_1818)=k5_relat_1(E_1821, F_1818) | ~m1_subset_1(F_1818, k1_zfmisc_1(k2_zfmisc_1(C_1819, D_1820))) | ~m1_subset_1(E_1821, k1_zfmisc_1(k2_zfmisc_1(A_1823, B_1822))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.51/7.74  tff(c_17770, plain, (![A_1827, B_1828, E_1829]: (k4_relset_1(A_1827, B_1828, '#skF_8', '#skF_9', E_1829, '#skF_11')=k5_relat_1(E_1829, '#skF_11') | ~m1_subset_1(E_1829, k1_zfmisc_1(k2_zfmisc_1(A_1827, B_1828))))), inference(resolution, [status(thm)], [c_38, c_17736])).
% 15.51/7.74  tff(c_17782, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_17770])).
% 15.51/7.74  tff(c_17786, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_17782, c_78])).
% 15.51/7.74  tff(c_26, plain, (![B_66, F_109, E_106, D_105, A_14]: (r2_hidden(k4_tarski(D_105, E_106), k5_relat_1(A_14, B_66)) | ~r2_hidden(k4_tarski(F_109, E_106), B_66) | ~r2_hidden(k4_tarski(D_105, F_109), A_14) | ~v1_relat_1(k5_relat_1(A_14, B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_17812, plain, (![D_105, A_14]: (r2_hidden(k4_tarski(D_105, '#skF_16'), k5_relat_1(A_14, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_105, '#skF_15'), A_14) | ~v1_relat_1(k5_relat_1(A_14, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_17786, c_26])).
% 15.51/7.74  tff(c_17900, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_17812])).
% 15.51/7.74  tff(c_17903, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_17900])).
% 15.51/7.74  tff(c_17907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_17903])).
% 15.51/7.74  tff(c_17909, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_17812])).
% 15.51/7.74  tff(c_17910, plain, (![D_1865, E_1866, A_1867, B_1868]: (r2_hidden(k4_tarski('#skF_1'(D_1865, E_1866, k5_relat_1(A_1867, B_1868), B_1868, A_1867), E_1866), B_1868) | ~r2_hidden(k4_tarski(D_1865, E_1866), k5_relat_1(A_1867, B_1868)) | ~v1_relat_1(k5_relat_1(A_1867, B_1868)) | ~v1_relat_1(B_1868) | ~v1_relat_1(A_1867))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_52, plain, (![H_337]: (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_17686, plain, (![H_337]: (~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 15.51/7.74  tff(c_17919, plain, (![D_1865, A_1867]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_1865, '#skF_16', k5_relat_1(A_1867, '#skF_11'), '#skF_11', A_1867)), '#skF_10') | ~m1_subset_1('#skF_1'(D_1865, '#skF_16', k5_relat_1(A_1867, '#skF_11'), '#skF_11', A_1867), '#skF_8') | ~r2_hidden(k4_tarski(D_1865, '#skF_16'), k5_relat_1(A_1867, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1867, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1867))), inference(resolution, [status(thm)], [c_17910, c_17686])).
% 15.51/7.74  tff(c_17988, plain, (![D_1879, A_1880]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_1879, '#skF_16', k5_relat_1(A_1880, '#skF_11'), '#skF_11', A_1880)), '#skF_10') | ~m1_subset_1('#skF_1'(D_1879, '#skF_16', k5_relat_1(A_1880, '#skF_11'), '#skF_11', A_1880), '#skF_8') | ~r2_hidden(k4_tarski(D_1879, '#skF_16'), k5_relat_1(A_1880, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1880, '#skF_11')) | ~v1_relat_1(A_1880))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_17919])).
% 15.51/7.74  tff(c_17992, plain, (~m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_17988])).
% 15.51/7.74  tff(c_17995, plain, (~m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_17909, c_17786, c_17992])).
% 15.51/7.74  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.51/7.74  tff(c_19046, plain, (![A_2067, B_2065, E_2069, D_2066, A_2068]: (r2_hidden(k4_tarski('#skF_1'(D_2066, E_2069, k5_relat_1(A_2067, B_2065), B_2065, A_2067), E_2069), A_2068) | ~m1_subset_1(B_2065, k1_zfmisc_1(A_2068)) | ~r2_hidden(k4_tarski(D_2066, E_2069), k5_relat_1(A_2067, B_2065)) | ~v1_relat_1(k5_relat_1(A_2067, B_2065)) | ~v1_relat_1(B_2065) | ~v1_relat_1(A_2067))), inference(resolution, [status(thm)], [c_17910, c_8])).
% 15.51/7.74  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.51/7.74  tff(c_20598, plain, (![A_2230, D_2228, D_2227, B_2229, E_2232, C_2231]: (r2_hidden('#skF_1'(D_2227, E_2232, k5_relat_1(A_2230, B_2229), B_2229, A_2230), C_2231) | ~m1_subset_1(B_2229, k1_zfmisc_1(k2_zfmisc_1(C_2231, D_2228))) | ~r2_hidden(k4_tarski(D_2227, E_2232), k5_relat_1(A_2230, B_2229)) | ~v1_relat_1(k5_relat_1(A_2230, B_2229)) | ~v1_relat_1(B_2229) | ~v1_relat_1(A_2230))), inference(resolution, [status(thm)], [c_19046, c_6])).
% 15.51/7.74  tff(c_20620, plain, (![D_2227, E_2232, A_2230]: (r2_hidden('#skF_1'(D_2227, E_2232, k5_relat_1(A_2230, '#skF_11'), '#skF_11', A_2230), '#skF_8') | ~r2_hidden(k4_tarski(D_2227, E_2232), k5_relat_1(A_2230, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_2230, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_2230))), inference(resolution, [status(thm)], [c_38, c_20598])).
% 15.51/7.74  tff(c_20644, plain, (![D_2236, E_2237, A_2238]: (r2_hidden('#skF_1'(D_2236, E_2237, k5_relat_1(A_2238, '#skF_11'), '#skF_11', A_2238), '#skF_8') | ~r2_hidden(k4_tarski(D_2236, E_2237), k5_relat_1(A_2238, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_2238, '#skF_11')) | ~v1_relat_1(A_2238))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_20620])).
% 15.51/7.74  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.51/7.74  tff(c_20854, plain, (![D_2245, E_2246, A_2247]: (m1_subset_1('#skF_1'(D_2245, E_2246, k5_relat_1(A_2247, '#skF_11'), '#skF_11', A_2247), '#skF_8') | ~r2_hidden(k4_tarski(D_2245, E_2246), k5_relat_1(A_2247, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_2247, '#skF_11')) | ~v1_relat_1(A_2247))), inference(resolution, [status(thm)], [c_20644, c_10])).
% 15.51/7.74  tff(c_20900, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_17786, c_20854])).
% 15.51/7.74  tff(c_20923, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_17909, c_20900])).
% 15.51/7.74  tff(c_20925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17995, c_20923])).
% 15.51/7.74  tff(c_20926, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10')), inference(splitRight, [status(thm)], [c_52])).
% 15.51/7.74  tff(c_9035, plain, (![E_1101, C_1099, B_1102, D_1100, A_1103, F_1098]: (k4_relset_1(A_1103, B_1102, C_1099, D_1100, E_1101, F_1098)=k5_relat_1(E_1101, F_1098) | ~m1_subset_1(F_1098, k1_zfmisc_1(k2_zfmisc_1(C_1099, D_1100))) | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1102))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.51/7.74  tff(c_9060, plain, (![A_1107, B_1108, E_1109]: (k4_relset_1(A_1107, B_1108, '#skF_8', '#skF_9', E_1109, '#skF_11')=k5_relat_1(E_1109, '#skF_11') | ~m1_subset_1(E_1109, k1_zfmisc_1(k2_zfmisc_1(A_1107, B_1108))))), inference(resolution, [status(thm)], [c_38, c_9035])).
% 15.51/7.74  tff(c_9067, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_9060])).
% 15.51/7.74  tff(c_9071, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_9067, c_78])).
% 15.51/7.74  tff(c_9090, plain, (![E_1112, F_1114, A_1115, B_1113, D_1111]: (r2_hidden(k4_tarski(D_1111, E_1112), k5_relat_1(A_1115, B_1113)) | ~r2_hidden(k4_tarski(F_1114, E_1112), B_1113) | ~r2_hidden(k4_tarski(D_1111, F_1114), A_1115) | ~v1_relat_1(k5_relat_1(A_1115, B_1113)) | ~v1_relat_1(B_1113) | ~v1_relat_1(A_1115))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_9095, plain, (![D_1111, A_1115]: (r2_hidden(k4_tarski(D_1111, '#skF_16'), k5_relat_1(A_1115, k5_relat_1('#skF_10', '#skF_11'))) | ~r2_hidden(k4_tarski(D_1111, '#skF_15'), A_1115) | ~v1_relat_1(k5_relat_1(A_1115, k5_relat_1('#skF_10', '#skF_11'))) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(A_1115))), inference(resolution, [status(thm)], [c_9071, c_9090])).
% 15.51/7.74  tff(c_9099, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_9095])).
% 15.51/7.74  tff(c_9102, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_9099])).
% 15.51/7.74  tff(c_9106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_9102])).
% 15.51/7.74  tff(c_9108, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_9095])).
% 15.51/7.74  tff(c_9122, plain, (![D_1123, E_1124, A_1125, B_1126]: (r2_hidden(k4_tarski(D_1123, '#skF_1'(D_1123, E_1124, k5_relat_1(A_1125, B_1126), B_1126, A_1125)), A_1125) | ~r2_hidden(k4_tarski(D_1123, E_1124), k5_relat_1(A_1125, B_1126)) | ~v1_relat_1(k5_relat_1(A_1125, B_1126)) | ~v1_relat_1(B_1126) | ~v1_relat_1(A_1125))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_9298, plain, (![D_1171, E_1170, A_1173, B_1172, A_1174]: (r2_hidden(k4_tarski(D_1171, '#skF_1'(D_1171, E_1170, k5_relat_1(A_1174, B_1172), B_1172, A_1174)), A_1173) | ~m1_subset_1(A_1174, k1_zfmisc_1(A_1173)) | ~r2_hidden(k4_tarski(D_1171, E_1170), k5_relat_1(A_1174, B_1172)) | ~v1_relat_1(k5_relat_1(A_1174, B_1172)) | ~v1_relat_1(B_1172) | ~v1_relat_1(A_1174))), inference(resolution, [status(thm)], [c_9122, c_8])).
% 15.51/7.74  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.51/7.74  tff(c_10665, plain, (![E_1358, B_1362, A_1357, D_1359, C_1361, D_1360]: (r2_hidden('#skF_1'(D_1360, E_1358, k5_relat_1(A_1357, B_1362), B_1362, A_1357), D_1359) | ~m1_subset_1(A_1357, k1_zfmisc_1(k2_zfmisc_1(C_1361, D_1359))) | ~r2_hidden(k4_tarski(D_1360, E_1358), k5_relat_1(A_1357, B_1362)) | ~v1_relat_1(k5_relat_1(A_1357, B_1362)) | ~v1_relat_1(B_1362) | ~v1_relat_1(A_1357))), inference(resolution, [status(thm)], [c_9298, c_4])).
% 15.51/7.74  tff(c_10685, plain, (![D_1360, E_1358, B_1362]: (r2_hidden('#skF_1'(D_1360, E_1358, k5_relat_1('#skF_10', B_1362), B_1362, '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski(D_1360, E_1358), k5_relat_1('#skF_10', B_1362)) | ~v1_relat_1(k5_relat_1('#skF_10', B_1362)) | ~v1_relat_1(B_1362) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_40, c_10665])).
% 15.51/7.74  tff(c_10700, plain, (![D_1363, E_1364, B_1365]: (r2_hidden('#skF_1'(D_1363, E_1364, k5_relat_1('#skF_10', B_1365), B_1365, '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski(D_1363, E_1364), k5_relat_1('#skF_10', B_1365)) | ~v1_relat_1(k5_relat_1('#skF_10', B_1365)) | ~v1_relat_1(B_1365))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10685])).
% 15.51/7.74  tff(c_10716, plain, (![D_1369, E_1370, B_1371]: (m1_subset_1('#skF_1'(D_1369, E_1370, k5_relat_1('#skF_10', B_1371), B_1371, '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski(D_1369, E_1370), k5_relat_1('#skF_10', B_1371)) | ~v1_relat_1(k5_relat_1('#skF_10', B_1371)) | ~v1_relat_1(B_1371))), inference(resolution, [status(thm)], [c_10700, c_10])).
% 15.51/7.74  tff(c_10751, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_9071, c_10716])).
% 15.51/7.74  tff(c_10767, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_9108, c_10751])).
% 15.51/7.74  tff(c_9160, plain, (![D_1132, E_1133, A_1134, B_1135]: (r2_hidden(k4_tarski('#skF_1'(D_1132, E_1133, k5_relat_1(A_1134, B_1135), B_1135, A_1134), E_1133), B_1135) | ~r2_hidden(k4_tarski(D_1132, E_1133), k5_relat_1(A_1134, B_1135)) | ~v1_relat_1(k5_relat_1(A_1134, B_1135)) | ~v1_relat_1(B_1135) | ~v1_relat_1(A_1134))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_50, plain, (![H_337]: (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11') | ~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_9032, plain, (![H_337]: (~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 15.51/7.74  tff(c_9169, plain, (![D_1132, A_1134]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_1132, '#skF_16', k5_relat_1(A_1134, '#skF_11'), '#skF_11', A_1134)), '#skF_10') | ~m1_subset_1('#skF_1'(D_1132, '#skF_16', k5_relat_1(A_1134, '#skF_11'), '#skF_11', A_1134), '#skF_8') | ~r2_hidden(k4_tarski(D_1132, '#skF_16'), k5_relat_1(A_1134, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1134, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1134))), inference(resolution, [status(thm)], [c_9160, c_9032])).
% 15.51/7.74  tff(c_17644, plain, (![D_1804, A_1805]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_1804, '#skF_16', k5_relat_1(A_1805, '#skF_11'), '#skF_11', A_1805)), '#skF_10') | ~m1_subset_1('#skF_1'(D_1804, '#skF_16', k5_relat_1(A_1805, '#skF_11'), '#skF_11', A_1805), '#skF_8') | ~r2_hidden(k4_tarski(D_1804, '#skF_16'), k5_relat_1(A_1805, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1805, '#skF_11')) | ~v1_relat_1(A_1805))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_9169])).
% 15.51/7.74  tff(c_17652, plain, (~m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_17644])).
% 15.51/7.74  tff(c_17659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_9108, c_9071, c_10767, c_17652])).
% 15.51/7.74  tff(c_17660, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_50])).
% 15.51/7.74  tff(c_21064, plain, (![B_2274, F_2275, D_2272, A_2276, E_2273]: (r2_hidden(k4_tarski(D_2272, E_2273), k5_relat_1(A_2276, B_2274)) | ~r2_hidden(k4_tarski(F_2275, E_2273), B_2274) | ~r2_hidden(k4_tarski(D_2272, F_2275), A_2276) | ~v1_relat_1(k5_relat_1(A_2276, B_2274)) | ~v1_relat_1(B_2274) | ~v1_relat_1(A_2276))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_21074, plain, (![D_2272, A_2276]: (r2_hidden(k4_tarski(D_2272, '#skF_13'), k5_relat_1(A_2276, '#skF_11')) | ~r2_hidden(k4_tarski(D_2272, '#skF_14'), A_2276) | ~v1_relat_1(k5_relat_1(A_2276, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_2276))), inference(resolution, [status(thm)], [c_17660, c_21064])).
% 15.51/7.74  tff(c_21272, plain, (![D_2301, A_2302]: (r2_hidden(k4_tarski(D_2301, '#skF_13'), k5_relat_1(A_2302, '#skF_11')) | ~r2_hidden(k4_tarski(D_2301, '#skF_14'), A_2302) | ~v1_relat_1(k5_relat_1(A_2302, '#skF_11')) | ~v1_relat_1(A_2302))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_21074])).
% 15.51/7.74  tff(c_21028, plain, (![A_2268, B_2269, E_2270]: (k4_relset_1(A_2268, B_2269, '#skF_8', '#skF_9', E_2270, '#skF_11')=k5_relat_1(E_2270, '#skF_11') | ~m1_subset_1(E_2270, k1_zfmisc_1(k2_zfmisc_1(A_2268, B_2269))))), inference(resolution, [status(thm)], [c_38, c_20966])).
% 15.51/7.74  tff(c_21045, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_21028])).
% 15.51/7.74  tff(c_48, plain, (![H_337]: (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | ~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_20985, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_48])).
% 15.51/7.74  tff(c_21048, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_21045, c_20985])).
% 15.51/7.74  tff(c_21277, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_21272, c_21048])).
% 15.51/7.74  tff(c_21286, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_20926, c_21277])).
% 15.51/7.74  tff(c_21291, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_21286])).
% 15.51/7.74  tff(c_21295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_21291])).
% 15.51/7.74  tff(c_21296, plain, (![H_337]: (~r2_hidden(k4_tarski(H_337, '#skF_16'), '#skF_11') | ~r2_hidden(k4_tarski('#skF_15', H_337), '#skF_10') | ~m1_subset_1(H_337, '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 15.51/7.74  tff(c_21519, plain, (![D_2335, A_2337]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_2335, '#skF_16', k5_relat_1(A_2337, '#skF_11'), '#skF_11', A_2337)), '#skF_10') | ~m1_subset_1('#skF_1'(D_2335, '#skF_16', k5_relat_1(A_2337, '#skF_11'), '#skF_11', A_2337), '#skF_8') | ~r2_hidden(k4_tarski(D_2335, '#skF_16'), k5_relat_1(A_2337, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_2337, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_2337))), inference(resolution, [status(thm)], [c_21514, c_21296])).
% 15.51/7.74  tff(c_21936, plain, (![D_2416, A_2417]: (~r2_hidden(k4_tarski('#skF_15', '#skF_1'(D_2416, '#skF_16', k5_relat_1(A_2417, '#skF_11'), '#skF_11', A_2417)), '#skF_10') | ~m1_subset_1('#skF_1'(D_2416, '#skF_16', k5_relat_1(A_2417, '#skF_11'), '#skF_11', A_2417), '#skF_8') | ~r2_hidden(k4_tarski(D_2416, '#skF_16'), k5_relat_1(A_2417, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_2417, '#skF_11')) | ~v1_relat_1(A_2417))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_21519])).
% 15.51/7.74  tff(c_21940, plain, (~m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_21936])).
% 15.51/7.74  tff(c_21943, plain, (~m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_21873, c_21370, c_21940])).
% 15.51/7.74  tff(c_22602, plain, (![B_2575, D_2579, E_2576, A_2578, A_2577]: (r2_hidden(k4_tarski('#skF_1'(D_2579, E_2576, k5_relat_1(A_2577, B_2575), B_2575, A_2577), E_2576), A_2578) | ~m1_subset_1(B_2575, k1_zfmisc_1(A_2578)) | ~r2_hidden(k4_tarski(D_2579, E_2576), k5_relat_1(A_2577, B_2575)) | ~v1_relat_1(k5_relat_1(A_2577, B_2575)) | ~v1_relat_1(B_2575) | ~v1_relat_1(A_2577))), inference(resolution, [status(thm)], [c_21514, c_8])).
% 15.51/7.74  tff(c_29142, plain, (![C_3081, D_3077, D_3078, E_3080, B_3082, A_3079]: (r2_hidden('#skF_1'(D_3077, E_3080, k5_relat_1(A_3079, B_3082), B_3082, A_3079), C_3081) | ~m1_subset_1(B_3082, k1_zfmisc_1(k2_zfmisc_1(C_3081, D_3078))) | ~r2_hidden(k4_tarski(D_3077, E_3080), k5_relat_1(A_3079, B_3082)) | ~v1_relat_1(k5_relat_1(A_3079, B_3082)) | ~v1_relat_1(B_3082) | ~v1_relat_1(A_3079))), inference(resolution, [status(thm)], [c_22602, c_6])).
% 15.51/7.74  tff(c_29278, plain, (![D_3077, E_3080, A_3079]: (r2_hidden('#skF_1'(D_3077, E_3080, k5_relat_1(A_3079, '#skF_11'), '#skF_11', A_3079), '#skF_8') | ~r2_hidden(k4_tarski(D_3077, E_3080), k5_relat_1(A_3079, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_3079, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_3079))), inference(resolution, [status(thm)], [c_38, c_29142])).
% 15.51/7.74  tff(c_29337, plain, (![D_3086, E_3087, A_3088]: (r2_hidden('#skF_1'(D_3086, E_3087, k5_relat_1(A_3088, '#skF_11'), '#skF_11', A_3088), '#skF_8') | ~r2_hidden(k4_tarski(D_3086, E_3087), k5_relat_1(A_3088, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_3088, '#skF_11')) | ~v1_relat_1(A_3088))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_29278])).
% 15.51/7.74  tff(c_29509, plain, (![D_3092, E_3093, A_3094]: (m1_subset_1('#skF_1'(D_3092, E_3093, k5_relat_1(A_3094, '#skF_11'), '#skF_11', A_3094), '#skF_8') | ~r2_hidden(k4_tarski(D_3092, E_3093), k5_relat_1(A_3094, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_3094, '#skF_11')) | ~v1_relat_1(A_3094))), inference(resolution, [status(thm)], [c_29337, c_10])).
% 15.51/7.74  tff(c_29624, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_21370, c_29509])).
% 15.51/7.74  tff(c_29677, plain, (m1_subset_1('#skF_1'('#skF_15', '#skF_16', k5_relat_1('#skF_10', '#skF_11'), '#skF_11', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_21873, c_29624])).
% 15.51/7.74  tff(c_29679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21943, c_29677])).
% 15.51/7.74  tff(c_29681, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_62])).
% 15.51/7.74  tff(c_60, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_29686, plain, (r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitLeft, [status(thm)], [c_60])).
% 15.51/7.74  tff(c_29687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29681, c_29686])).
% 15.51/7.74  tff(c_29688, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10')), inference(splitRight, [status(thm)], [c_60])).
% 15.51/7.74  tff(c_29689, plain, (~r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_60])).
% 15.51/7.74  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11') | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_29767, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_13'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_29689, c_58])).
% 15.51/7.74  tff(c_29930, plain, (![B_3151, D_3149, A_3153, E_3150, F_3152]: (r2_hidden(k4_tarski(D_3149, E_3150), k5_relat_1(A_3153, B_3151)) | ~r2_hidden(k4_tarski(F_3152, E_3150), B_3151) | ~r2_hidden(k4_tarski(D_3149, F_3152), A_3153) | ~v1_relat_1(k5_relat_1(A_3153, B_3151)) | ~v1_relat_1(B_3151) | ~v1_relat_1(A_3153))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.51/7.74  tff(c_29934, plain, (![D_3149, A_3153]: (r2_hidden(k4_tarski(D_3149, '#skF_13'), k5_relat_1(A_3153, '#skF_11')) | ~r2_hidden(k4_tarski(D_3149, '#skF_14'), A_3153) | ~v1_relat_1(k5_relat_1(A_3153, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_3153))), inference(resolution, [status(thm)], [c_29767, c_29930])).
% 15.51/7.74  tff(c_29993, plain, (![D_3167, A_3168]: (r2_hidden(k4_tarski(D_3167, '#skF_13'), k5_relat_1(A_3168, '#skF_11')) | ~r2_hidden(k4_tarski(D_3167, '#skF_14'), A_3168) | ~v1_relat_1(k5_relat_1(A_3168, '#skF_11')) | ~v1_relat_1(A_3168))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_29934])).
% 15.51/7.74  tff(c_29858, plain, (![D_3139, E_3140, F_3137, B_3141, A_3142, C_3138]: (k4_relset_1(A_3142, B_3141, C_3138, D_3139, E_3140, F_3137)=k5_relat_1(E_3140, F_3137) | ~m1_subset_1(F_3137, k1_zfmisc_1(k2_zfmisc_1(C_3138, D_3139))) | ~m1_subset_1(E_3140, k1_zfmisc_1(k2_zfmisc_1(A_3142, B_3141))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.51/7.74  tff(c_29900, plain, (![A_3146, B_3147, E_3148]: (k4_relset_1(A_3146, B_3147, '#skF_8', '#skF_9', E_3148, '#skF_11')=k5_relat_1(E_3148, '#skF_11') | ~m1_subset_1(E_3148, k1_zfmisc_1(k2_zfmisc_1(A_3146, B_3147))))), inference(resolution, [status(thm)], [c_38, c_29858])).
% 15.51/7.74  tff(c_29917, plain, (k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')=k5_relat_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_29900])).
% 15.51/7.74  tff(c_56, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11')) | r2_hidden(k4_tarski('#skF_15', '#skF_16'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.51/7.74  tff(c_29839, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k4_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_9', '#skF_10', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_29689, c_56])).
% 15.51/7.74  tff(c_29919, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_29917, c_29839])).
% 15.51/7.74  tff(c_29998, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_14'), '#skF_10') | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_29993, c_29919])).
% 15.51/7.74  tff(c_30007, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_29688, c_29998])).
% 15.51/7.74  tff(c_30012, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_30007])).
% 15.51/7.74  tff(c_30016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_30012])).
% 15.51/7.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.51/7.74  
% 15.51/7.74  Inference rules
% 15.51/7.74  ----------------------
% 15.51/7.74  #Ref     : 0
% 15.51/7.74  #Sup     : 6733
% 15.51/7.74  #Fact    : 0
% 15.51/7.74  #Define  : 0
% 15.51/7.74  #Split   : 92
% 15.51/7.74  #Chain   : 0
% 15.51/7.74  #Close   : 0
% 15.51/7.74  
% 15.51/7.74  Ordering : KBO
% 15.51/7.74  
% 15.51/7.74  Simplification rules
% 15.51/7.74  ----------------------
% 15.51/7.74  #Subsume      : 261
% 15.51/7.74  #Demod        : 881
% 15.51/7.74  #Tautology    : 234
% 15.51/7.74  #SimpNegUnit  : 5
% 15.51/7.74  #BackRed      : 20
% 15.51/7.75  
% 15.51/7.75  #Partial instantiations: 0
% 15.51/7.75  #Strategies tried      : 1
% 15.51/7.75  
% 15.51/7.75  Timing (in seconds)
% 15.51/7.75  ----------------------
% 15.51/7.75  Preprocessing        : 0.34
% 15.51/7.75  Parsing              : 0.17
% 15.51/7.75  CNF conversion       : 0.05
% 15.51/7.75  Main loop            : 6.51
% 15.51/7.75  Inferencing          : 2.02
% 15.51/7.75  Reduction            : 1.68
% 15.51/7.75  Demodulation         : 1.18
% 15.51/7.75  BG Simplification    : 0.30
% 15.51/7.75  Subsumption          : 1.96
% 15.51/7.75  Abstraction          : 0.63
% 15.51/7.75  MUC search           : 0.00
% 15.51/7.75  Cooper               : 0.00
% 15.51/7.75  Total                : 6.91
% 15.51/7.75  Index Insertion      : 0.00
% 15.51/7.75  Index Deletion       : 0.00
% 15.51/7.75  Index Matching       : 0.00
% 15.51/7.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
