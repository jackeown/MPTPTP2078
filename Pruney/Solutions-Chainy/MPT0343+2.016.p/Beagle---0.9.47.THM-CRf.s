%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 601 expanded)
%              Number of leaves         :   18 ( 208 expanded)
%              Depth                    :   19
%              Number of atoms          :  176 (1890 expanded)
%              Number of equality atoms :   19 ( 379 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_22,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),B_41)
      | r2_hidden('#skF_3'(A_40,B_41),A_40)
      | B_41 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_63,B_64,B_65] :
      ( r2_hidden('#skF_3'(A_63,B_64),B_65)
      | ~ r1_tarski(A_63,B_65)
      | r2_hidden('#skF_2'(A_63,B_64),B_64)
      | B_64 = A_63 ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_257,plain,(
    ! [A_66,B_67] :
      ( ~ r1_tarski(A_66,B_67)
      | r2_hidden('#skF_2'(A_66,B_67),B_67)
      | B_67 = A_66 ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_28,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_6')
      | ~ r2_hidden(D_20,'#skF_7')
      | ~ m1_subset_1(D_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_284,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_2'(A_68,'#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_68,'#skF_7'),'#skF_5')
      | ~ r1_tarski(A_68,'#skF_7')
      | A_68 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_290,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_284,c_8])).

tff(c_300,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_290])).

tff(c_324,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_9,B_10,C_14] :
      ( m1_subset_1('#skF_4'(A_9,B_10,C_14),A_9)
      | r1_tarski(B_10,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_9,B_10,C_14] :
      ( r2_hidden('#skF_4'(A_9,B_10,C_14),B_10)
      | r1_tarski(B_10,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_7')
      | ~ r2_hidden(D_20,'#skF_6')
      | ~ m1_subset_1(D_20,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_377,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r2_hidden('#skF_4'(A_76,B_77,C_78),C_78)
      | r1_tarski(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_853,plain,(
    ! [B_130,A_131] :
      ( r1_tarski(B_130,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_131))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ r2_hidden('#skF_4'(A_131,B_130,'#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_131,B_130,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_377])).

tff(c_865,plain,(
    ! [A_9] :
      ( ~ m1_subset_1('#skF_4'(A_9,'#skF_6','#skF_7'),'#skF_5')
      | r1_tarski('#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_18,c_853])).

tff(c_877,plain,(
    ! [A_134] :
      ( ~ m1_subset_1('#skF_4'(A_134,'#skF_6','#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_134))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_134)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_324,c_865])).

tff(c_881,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_877])).

tff(c_884,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_881])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_884])).

tff(c_888,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_120,plain,(
    ! [A_40,B_41,B_2] :
      ( r2_hidden('#skF_3'(A_40,B_41),B_2)
      | ~ r1_tarski(A_40,B_2)
      | r2_hidden('#skF_2'(A_40,B_41),B_41)
      | B_41 = A_40 ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_887,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_909,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_912,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_120,c_909])).

tff(c_918,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_912])).

tff(c_919,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_918])).

tff(c_928,plain,(
    ! [B_137] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_137)
      | ~ r1_tarski('#skF_7',B_137) ) ),
    inference(resolution,[status(thm)],[c_919,c_2])).

tff(c_122,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_2'(A_42,B_43),A_42)
      | r2_hidden('#skF_3'(A_42,B_43),A_42)
      | B_43 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [A_42,B_43,B_2] :
      ( r2_hidden('#skF_3'(A_42,B_43),B_2)
      | ~ r1_tarski(A_42,B_2)
      | ~ r2_hidden('#skF_2'(A_42,B_43),A_42)
      | B_43 = A_42 ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_931,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_7'),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | '#skF_7' = '#skF_6'
      | ~ r1_tarski('#skF_7','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_928,c_139])).

tff(c_946,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_7'),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | ~ r1_tarski('#skF_7','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_931])).

tff(c_968,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_141,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_4'(A_44,B_45,C_46),B_45)
      | r1_tarski(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1729,plain,(
    ! [A_212,C_213] :
      ( r2_hidden('#skF_4'(A_212,'#skF_7',C_213),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_212,'#skF_7',C_213),'#skF_5')
      | r1_tarski('#skF_7',C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(A_212))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_141,c_28])).

tff(c_16,plain,(
    ! [A_9,B_10,C_14] :
      ( ~ r2_hidden('#skF_4'(A_9,B_10,C_14),C_14)
      | r1_tarski(B_10,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1733,plain,(
    ! [A_212] :
      ( ~ m1_subset_1('#skF_4'(A_212,'#skF_7','#skF_6'),'#skF_5')
      | r1_tarski('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_212))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_1729,c_16])).

tff(c_1743,plain,(
    ! [A_214] :
      ( ~ m1_subset_1('#skF_4'(A_214,'#skF_7','#skF_6'),'#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_214))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_214)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_968,c_1733])).

tff(c_1747,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_1743])).

tff(c_1750,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_1747])).

tff(c_1752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1750])).

tff(c_1758,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_7'),B_215)
      | ~ r1_tarski('#skF_6',B_215) ) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_1761,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1758,c_909])).

tff(c_1778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1761])).

tff(c_1780,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_1786,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1780,c_10])).

tff(c_1794,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1786])).

tff(c_1839,plain,(
    ! [B_220] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_220)
      | ~ r1_tarski('#skF_7',B_220) ) ),
    inference(resolution,[status(thm)],[c_1794,c_2])).

tff(c_1845,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1839,c_8])).

tff(c_1860,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_1845])).

tff(c_1861,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1860])).

tff(c_2612,plain,(
    ! [A_290,C_291] :
      ( r2_hidden('#skF_4'(A_290,'#skF_7',C_291),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_290,'#skF_7',C_291),'#skF_5')
      | r1_tarski('#skF_7',C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(A_290))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_290)) ) ),
    inference(resolution,[status(thm)],[c_141,c_28])).

tff(c_2616,plain,(
    ! [A_290] :
      ( ~ m1_subset_1('#skF_4'(A_290,'#skF_7','#skF_6'),'#skF_5')
      | r1_tarski('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_290))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_290)) ) ),
    inference(resolution,[status(thm)],[c_2612,c_16])).

tff(c_2626,plain,(
    ! [A_292] :
      ( ~ m1_subset_1('#skF_4'(A_292,'#skF_7','#skF_6'),'#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_292))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_292)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_1861,c_2616])).

tff(c_2630,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_2626])).

tff(c_2633,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_2630])).

tff(c_2635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_2633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.89  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 4.82/1.89  
% 4.82/1.89  %Foreground sorts:
% 4.82/1.89  
% 4.82/1.89  
% 4.82/1.89  %Background operators:
% 4.82/1.89  
% 4.82/1.89  
% 4.82/1.89  %Foreground operators:
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.82/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.82/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.82/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.82/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.82/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.89  
% 4.82/1.91  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 4.82/1.91  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.82/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.82/1.91  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 4.82/1.91  tff(c_22, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.91  tff(c_96, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), B_41) | r2_hidden('#skF_3'(A_40, B_41), A_40) | B_41=A_40)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.82/1.91  tff(c_224, plain, (![A_63, B_64, B_65]: (r2_hidden('#skF_3'(A_63, B_64), B_65) | ~r1_tarski(A_63, B_65) | r2_hidden('#skF_2'(A_63, B_64), B_64) | B_64=A_63)), inference(resolution, [status(thm)], [c_96, c_2])).
% 4.82/1.91  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.91  tff(c_257, plain, (![A_66, B_67]: (~r1_tarski(A_66, B_67) | r2_hidden('#skF_2'(A_66, B_67), B_67) | B_67=A_66)), inference(resolution, [status(thm)], [c_224, c_10])).
% 4.82/1.91  tff(c_28, plain, (![D_20]: (r2_hidden(D_20, '#skF_6') | ~r2_hidden(D_20, '#skF_7') | ~m1_subset_1(D_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.91  tff(c_284, plain, (![A_68]: (r2_hidden('#skF_2'(A_68, '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_2'(A_68, '#skF_7'), '#skF_5') | ~r1_tarski(A_68, '#skF_7') | A_68='#skF_7')), inference(resolution, [status(thm)], [c_257, c_28])).
% 4.82/1.91  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.91  tff(c_290, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_284, c_8])).
% 4.82/1.91  tff(c_300, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_290])).
% 4.82/1.91  tff(c_324, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_300])).
% 4.82/1.91  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.91  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.91  tff(c_20, plain, (![A_9, B_10, C_14]: (m1_subset_1('#skF_4'(A_9, B_10, C_14), A_9) | r1_tarski(B_10, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.91  tff(c_18, plain, (![A_9, B_10, C_14]: (r2_hidden('#skF_4'(A_9, B_10, C_14), B_10) | r1_tarski(B_10, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.91  tff(c_30, plain, (![D_20]: (r2_hidden(D_20, '#skF_7') | ~r2_hidden(D_20, '#skF_6') | ~m1_subset_1(D_20, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.91  tff(c_377, plain, (![A_76, B_77, C_78]: (~r2_hidden('#skF_4'(A_76, B_77, C_78), C_78) | r1_tarski(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.91  tff(c_853, plain, (![B_130, A_131]: (r1_tarski(B_130, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_131)) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~r2_hidden('#skF_4'(A_131, B_130, '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_4'(A_131, B_130, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_377])).
% 4.82/1.91  tff(c_865, plain, (![A_9]: (~m1_subset_1('#skF_4'(A_9, '#skF_6', '#skF_7'), '#skF_5') | r1_tarski('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_9)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_18, c_853])).
% 4.82/1.91  tff(c_877, plain, (![A_134]: (~m1_subset_1('#skF_4'(A_134, '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_134)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_134)))), inference(negUnitSimplification, [status(thm)], [c_324, c_324, c_865])).
% 4.82/1.91  tff(c_881, plain, (r1_tarski('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_877])).
% 4.82/1.91  tff(c_884, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_881])).
% 4.82/1.91  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_324, c_884])).
% 4.82/1.91  tff(c_888, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_300])).
% 4.82/1.91  tff(c_120, plain, (![A_40, B_41, B_2]: (r2_hidden('#skF_3'(A_40, B_41), B_2) | ~r1_tarski(A_40, B_2) | r2_hidden('#skF_2'(A_40, B_41), B_41) | B_41=A_40)), inference(resolution, [status(thm)], [c_96, c_2])).
% 4.82/1.91  tff(c_887, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_300])).
% 4.82/1.91  tff(c_909, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_887])).
% 4.82/1.91  tff(c_912, plain, (~r1_tarski('#skF_6', '#skF_7') | r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_120, c_909])).
% 4.82/1.91  tff(c_918, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_888, c_912])).
% 4.82/1.91  tff(c_919, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_22, c_918])).
% 4.82/1.91  tff(c_928, plain, (![B_137]: (r2_hidden('#skF_2'('#skF_6', '#skF_7'), B_137) | ~r1_tarski('#skF_7', B_137))), inference(resolution, [status(thm)], [c_919, c_2])).
% 4.82/1.91  tff(c_122, plain, (![A_42, B_43]: (~r2_hidden('#skF_2'(A_42, B_43), A_42) | r2_hidden('#skF_3'(A_42, B_43), A_42) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.91  tff(c_139, plain, (![A_42, B_43, B_2]: (r2_hidden('#skF_3'(A_42, B_43), B_2) | ~r1_tarski(A_42, B_2) | ~r2_hidden('#skF_2'(A_42, B_43), A_42) | B_43=A_42)), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.82/1.91  tff(c_931, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_6', '#skF_7'), B_2) | ~r1_tarski('#skF_6', B_2) | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_928, c_139])).
% 4.82/1.91  tff(c_946, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_6', '#skF_7'), B_2) | ~r1_tarski('#skF_6', B_2) | ~r1_tarski('#skF_7', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_22, c_931])).
% 4.82/1.91  tff(c_968, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_946])).
% 4.82/1.91  tff(c_141, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_4'(A_44, B_45, C_46), B_45) | r1_tarski(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.91  tff(c_1729, plain, (![A_212, C_213]: (r2_hidden('#skF_4'(A_212, '#skF_7', C_213), '#skF_6') | ~m1_subset_1('#skF_4'(A_212, '#skF_7', C_213), '#skF_5') | r1_tarski('#skF_7', C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(A_212)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_212)))), inference(resolution, [status(thm)], [c_141, c_28])).
% 4.82/1.91  tff(c_16, plain, (![A_9, B_10, C_14]: (~r2_hidden('#skF_4'(A_9, B_10, C_14), C_14) | r1_tarski(B_10, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.82/1.91  tff(c_1733, plain, (![A_212]: (~m1_subset_1('#skF_4'(A_212, '#skF_7', '#skF_6'), '#skF_5') | r1_tarski('#skF_7', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_212)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_212)))), inference(resolution, [status(thm)], [c_1729, c_16])).
% 4.82/1.91  tff(c_1743, plain, (![A_214]: (~m1_subset_1('#skF_4'(A_214, '#skF_7', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_214)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_214)))), inference(negUnitSimplification, [status(thm)], [c_968, c_968, c_1733])).
% 4.82/1.91  tff(c_1747, plain, (r1_tarski('#skF_7', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_1743])).
% 4.82/1.91  tff(c_1750, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_1747])).
% 4.82/1.91  tff(c_1752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_968, c_1750])).
% 4.82/1.91  tff(c_1758, plain, (![B_215]: (r2_hidden('#skF_3'('#skF_6', '#skF_7'), B_215) | ~r1_tarski('#skF_6', B_215))), inference(splitRight, [status(thm)], [c_946])).
% 4.82/1.91  tff(c_1761, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1758, c_909])).
% 4.82/1.91  tff(c_1778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_888, c_1761])).
% 4.82/1.91  tff(c_1780, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_887])).
% 4.82/1.91  tff(c_1786, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1780, c_10])).
% 4.82/1.91  tff(c_1794, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_22, c_1786])).
% 4.82/1.91  tff(c_1839, plain, (![B_220]: (r2_hidden('#skF_2'('#skF_6', '#skF_7'), B_220) | ~r1_tarski('#skF_7', B_220))), inference(resolution, [status(thm)], [c_1794, c_2])).
% 4.82/1.91  tff(c_1845, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1839, c_8])).
% 4.82/1.91  tff(c_1860, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_1845])).
% 4.82/1.91  tff(c_1861, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_22, c_1860])).
% 4.82/1.91  tff(c_2612, plain, (![A_290, C_291]: (r2_hidden('#skF_4'(A_290, '#skF_7', C_291), '#skF_6') | ~m1_subset_1('#skF_4'(A_290, '#skF_7', C_291), '#skF_5') | r1_tarski('#skF_7', C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(A_290)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_290)))), inference(resolution, [status(thm)], [c_141, c_28])).
% 4.82/1.91  tff(c_2616, plain, (![A_290]: (~m1_subset_1('#skF_4'(A_290, '#skF_7', '#skF_6'), '#skF_5') | r1_tarski('#skF_7', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_290)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_290)))), inference(resolution, [status(thm)], [c_2612, c_16])).
% 4.82/1.91  tff(c_2626, plain, (![A_292]: (~m1_subset_1('#skF_4'(A_292, '#skF_7', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_292)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_292)))), inference(negUnitSimplification, [status(thm)], [c_1861, c_1861, c_2616])).
% 4.82/1.91  tff(c_2630, plain, (r1_tarski('#skF_7', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_2626])).
% 4.82/1.91  tff(c_2633, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_2630])).
% 4.82/1.91  tff(c_2635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1861, c_2633])).
% 4.82/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.91  
% 4.82/1.91  Inference rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Ref     : 0
% 4.82/1.91  #Sup     : 502
% 4.82/1.91  #Fact    : 0
% 4.82/1.91  #Define  : 0
% 4.82/1.91  #Split   : 20
% 4.82/1.91  #Chain   : 0
% 4.82/1.91  #Close   : 0
% 4.82/1.91  
% 4.82/1.91  Ordering : KBO
% 4.82/1.91  
% 4.82/1.91  Simplification rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Subsume      : 228
% 4.82/1.91  #Demod        : 127
% 4.82/1.91  #Tautology    : 65
% 4.82/1.91  #SimpNegUnit  : 68
% 4.82/1.91  #BackRed      : 0
% 4.82/1.91  
% 4.82/1.91  #Partial instantiations: 0
% 4.82/1.91  #Strategies tried      : 1
% 4.82/1.91  
% 4.82/1.91  Timing (in seconds)
% 4.82/1.91  ----------------------
% 4.82/1.92  Preprocessing        : 0.28
% 4.82/1.92  Parsing              : 0.15
% 4.82/1.92  CNF conversion       : 0.02
% 4.82/1.92  Main loop            : 0.86
% 4.82/1.92  Inferencing          : 0.32
% 4.82/1.92  Reduction            : 0.21
% 4.82/1.92  Demodulation         : 0.13
% 4.82/1.92  BG Simplification    : 0.03
% 4.82/1.92  Subsumption          : 0.25
% 4.82/1.92  Abstraction          : 0.03
% 4.82/1.92  MUC search           : 0.00
% 4.82/1.92  Cooper               : 0.00
% 4.82/1.92  Total                : 1.18
% 4.82/1.92  Index Insertion      : 0.00
% 4.82/1.92  Index Deletion       : 0.00
% 4.82/1.92  Index Matching       : 0.00
% 4.82/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
