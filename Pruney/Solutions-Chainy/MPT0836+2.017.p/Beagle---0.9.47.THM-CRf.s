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
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 12.60s
% Output     : CNFRefutation 12.60s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 130 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 299 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13180,plain,(
    ! [A_692,B_693,C_694] :
      ( k1_relset_1(A_692,B_693,C_694) = k1_relat_1(C_694)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(A_692,B_693))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_13184,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_13180])).

tff(c_202,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_206,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_202])).

tff(c_44,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7'))
    | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_14,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_14])).

tff(c_71,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_71])).

tff(c_34,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | ~ r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    ! [E_105] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_105),'#skF_7')
      | ~ m1_subset_1(E_105,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_75,c_34])).

tff(c_181,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_170])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_181])).

tff(c_192,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_231,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_192])).

tff(c_207,plain,(
    ! [C_110,A_111] :
      ( r2_hidden(k4_tarski(C_110,'#skF_4'(A_111,k1_relat_1(A_111),C_110)),A_111)
      | ~ r2_hidden(C_110,k1_relat_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1868,plain,(
    ! [C_271,A_272,A_273] :
      ( r2_hidden(k4_tarski(C_271,'#skF_4'(A_272,k1_relat_1(A_272),C_271)),A_273)
      | ~ m1_subset_1(A_272,k1_zfmisc_1(A_273))
      | ~ r2_hidden(C_271,k1_relat_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13071,plain,(
    ! [A_670,C_671,D_672,C_673] :
      ( r2_hidden('#skF_4'(A_670,k1_relat_1(A_670),C_671),D_672)
      | ~ m1_subset_1(A_670,k1_zfmisc_1(k2_zfmisc_1(C_673,D_672)))
      | ~ r2_hidden(C_671,k1_relat_1(A_670)) ) ),
    inference(resolution,[status(thm)],[c_1868,c_4])).

tff(c_13107,plain,(
    ! [C_674] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_674),'#skF_6')
      | ~ r2_hidden(C_674,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_28,c_13071])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13148,plain,(
    ! [C_675] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_675),'#skF_6')
      | ~ r2_hidden(C_675,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_13107,c_10])).

tff(c_12,plain,(
    ! [C_26,A_11] :
      ( r2_hidden(k4_tarski(C_26,'#skF_4'(A_11,k1_relat_1(A_11),C_26)),A_11)
      | ~ r2_hidden(C_26,k1_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_193,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_245,plain,(
    ! [E_112] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_112),'#skF_7')
      | ~ m1_subset_1(E_112,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_38])).

tff(c_249,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_252,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_249])).

tff(c_13155,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_13148,c_252])).

tff(c_13162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_13155])).

tff(c_13163,plain,(
    r2_hidden('#skF_8',k1_relset_1('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_13187,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13184,c_13163])).

tff(c_13201,plain,(
    ! [C_696,A_697] :
      ( r2_hidden(k4_tarski(C_696,'#skF_4'(A_697,k1_relat_1(A_697),C_696)),A_697)
      | ~ r2_hidden(C_696,k1_relat_1(A_697)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14712,plain,(
    ! [C_847,A_848,A_849] :
      ( r2_hidden(k4_tarski(C_847,'#skF_4'(A_848,k1_relat_1(A_848),C_847)),A_849)
      | ~ m1_subset_1(A_848,k1_zfmisc_1(A_849))
      | ~ r2_hidden(C_847,k1_relat_1(A_848)) ) ),
    inference(resolution,[status(thm)],[c_13201,c_8])).

tff(c_24594,plain,(
    ! [A_1192,C_1193,D_1194,C_1195] :
      ( r2_hidden('#skF_4'(A_1192,k1_relat_1(A_1192),C_1193),D_1194)
      | ~ m1_subset_1(A_1192,k1_zfmisc_1(k2_zfmisc_1(C_1195,D_1194)))
      | ~ r2_hidden(C_1193,k1_relat_1(A_1192)) ) ),
    inference(resolution,[status(thm)],[c_14712,c_4])).

tff(c_24622,plain,(
    ! [C_1196] :
      ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_1196),'#skF_6')
      | ~ r2_hidden(C_1196,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_28,c_24594])).

tff(c_24657,plain,(
    ! [C_1197] :
      ( m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),C_1197),'#skF_6')
      | ~ r2_hidden(C_1197,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24622,c_10])).

tff(c_13164,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13165,plain,(
    ! [E_74] :
      ( ~ r2_hidden(k4_tarski('#skF_8',E_74),'#skF_7')
      | ~ m1_subset_1(E_74,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_13164,c_42])).

tff(c_13218,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_13201,c_13165])).

tff(c_13228,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13187,c_13218])).

tff(c_24664,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_24657,c_13228])).

tff(c_24671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13187,c_24664])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 13:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.60/5.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/5.09  
% 12.60/5.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/5.09  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 12.60/5.09  
% 12.60/5.09  %Foreground sorts:
% 12.60/5.09  
% 12.60/5.09  
% 12.60/5.09  %Background operators:
% 12.60/5.09  
% 12.60/5.09  
% 12.60/5.09  %Foreground operators:
% 12.60/5.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.60/5.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.60/5.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.60/5.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 12.60/5.09  tff('#skF_7', type, '#skF_7': $i).
% 12.60/5.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.60/5.09  tff('#skF_5', type, '#skF_5': $i).
% 12.60/5.09  tff('#skF_6', type, '#skF_6': $i).
% 12.60/5.09  tff('#skF_9', type, '#skF_9': $i).
% 12.60/5.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.60/5.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.60/5.09  tff('#skF_8', type, '#skF_8': $i).
% 12.60/5.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.60/5.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.60/5.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.60/5.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.60/5.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.60/5.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.60/5.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.60/5.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.60/5.09  
% 12.60/5.11  tff(f_75, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 12.60/5.11  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.60/5.11  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 12.60/5.11  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 12.60/5.11  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 12.60/5.11  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 12.60/5.11  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_13180, plain, (![A_692, B_693, C_694]: (k1_relset_1(A_692, B_693, C_694)=k1_relat_1(C_694) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(A_692, B_693))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.60/5.11  tff(c_13184, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_13180])).
% 12.60/5.11  tff(c_202, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.60/5.11  tff(c_206, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_202])).
% 12.60/5.11  tff(c_44, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_46, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_44])).
% 12.60/5.11  tff(c_40, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')) | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_52, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_40])).
% 12.60/5.11  tff(c_14, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.60/5.11  tff(c_62, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_52, c_14])).
% 12.60/5.11  tff(c_71, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.60/5.11  tff(c_75, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_71])).
% 12.60/5.11  tff(c_34, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | ~r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_170, plain, (![E_105]: (~r2_hidden(k4_tarski('#skF_8', E_105), '#skF_7') | ~m1_subset_1(E_105, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_75, c_34])).
% 12.60/5.11  tff(c_181, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_170])).
% 12.60/5.11  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_181])).
% 12.60/5.11  tff(c_192, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_40])).
% 12.60/5.11  tff(c_231, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_192])).
% 12.60/5.11  tff(c_207, plain, (![C_110, A_111]: (r2_hidden(k4_tarski(C_110, '#skF_4'(A_111, k1_relat_1(A_111), C_110)), A_111) | ~r2_hidden(C_110, k1_relat_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.60/5.11  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.60/5.11  tff(c_1868, plain, (![C_271, A_272, A_273]: (r2_hidden(k4_tarski(C_271, '#skF_4'(A_272, k1_relat_1(A_272), C_271)), A_273) | ~m1_subset_1(A_272, k1_zfmisc_1(A_273)) | ~r2_hidden(C_271, k1_relat_1(A_272)))), inference(resolution, [status(thm)], [c_207, c_8])).
% 12.60/5.11  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.60/5.11  tff(c_13071, plain, (![A_670, C_671, D_672, C_673]: (r2_hidden('#skF_4'(A_670, k1_relat_1(A_670), C_671), D_672) | ~m1_subset_1(A_670, k1_zfmisc_1(k2_zfmisc_1(C_673, D_672))) | ~r2_hidden(C_671, k1_relat_1(A_670)))), inference(resolution, [status(thm)], [c_1868, c_4])).
% 12.60/5.11  tff(c_13107, plain, (![C_674]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_674), '#skF_6') | ~r2_hidden(C_674, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_28, c_13071])).
% 12.60/5.11  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.60/5.11  tff(c_13148, plain, (![C_675]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_675), '#skF_6') | ~r2_hidden(C_675, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_13107, c_10])).
% 12.60/5.11  tff(c_12, plain, (![C_26, A_11]: (r2_hidden(k4_tarski(C_26, '#skF_4'(A_11, k1_relat_1(A_11), C_26)), A_11) | ~r2_hidden(C_26, k1_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.60/5.11  tff(c_193, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 12.60/5.11  tff(c_38, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_245, plain, (![E_112]: (~r2_hidden(k4_tarski('#skF_8', E_112), '#skF_7') | ~m1_subset_1(E_112, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_193, c_38])).
% 12.60/5.11  tff(c_249, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_245])).
% 12.60/5.11  tff(c_252, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_249])).
% 12.60/5.11  tff(c_13155, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_13148, c_252])).
% 12.60/5.11  tff(c_13162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_13155])).
% 12.60/5.11  tff(c_13163, plain, (r2_hidden('#skF_8', k1_relset_1('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 12.60/5.11  tff(c_13187, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_13184, c_13163])).
% 12.60/5.11  tff(c_13201, plain, (![C_696, A_697]: (r2_hidden(k4_tarski(C_696, '#skF_4'(A_697, k1_relat_1(A_697), C_696)), A_697) | ~r2_hidden(C_696, k1_relat_1(A_697)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.60/5.11  tff(c_14712, plain, (![C_847, A_848, A_849]: (r2_hidden(k4_tarski(C_847, '#skF_4'(A_848, k1_relat_1(A_848), C_847)), A_849) | ~m1_subset_1(A_848, k1_zfmisc_1(A_849)) | ~r2_hidden(C_847, k1_relat_1(A_848)))), inference(resolution, [status(thm)], [c_13201, c_8])).
% 12.60/5.11  tff(c_24594, plain, (![A_1192, C_1193, D_1194, C_1195]: (r2_hidden('#skF_4'(A_1192, k1_relat_1(A_1192), C_1193), D_1194) | ~m1_subset_1(A_1192, k1_zfmisc_1(k2_zfmisc_1(C_1195, D_1194))) | ~r2_hidden(C_1193, k1_relat_1(A_1192)))), inference(resolution, [status(thm)], [c_14712, c_4])).
% 12.60/5.11  tff(c_24622, plain, (![C_1196]: (r2_hidden('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_1196), '#skF_6') | ~r2_hidden(C_1196, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_28, c_24594])).
% 12.60/5.11  tff(c_24657, plain, (![C_1197]: (m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), C_1197), '#skF_6') | ~r2_hidden(C_1197, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_24622, c_10])).
% 12.60/5.11  tff(c_13164, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 12.60/5.11  tff(c_42, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6') | m1_subset_1('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.60/5.11  tff(c_13165, plain, (![E_74]: (~r2_hidden(k4_tarski('#skF_8', E_74), '#skF_7') | ~m1_subset_1(E_74, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_13164, c_42])).
% 12.60/5.11  tff(c_13218, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_13201, c_13165])).
% 12.60/5.11  tff(c_13228, plain, (~m1_subset_1('#skF_4'('#skF_7', k1_relat_1('#skF_7'), '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13187, c_13218])).
% 12.60/5.11  tff(c_24664, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_24657, c_13228])).
% 12.60/5.11  tff(c_24671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13187, c_24664])).
% 12.60/5.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/5.11  
% 12.60/5.11  Inference rules
% 12.60/5.11  ----------------------
% 12.60/5.11  #Ref     : 0
% 12.60/5.11  #Sup     : 6483
% 12.60/5.11  #Fact    : 6
% 12.60/5.11  #Define  : 0
% 12.60/5.11  #Split   : 17
% 12.60/5.11  #Chain   : 0
% 12.60/5.11  #Close   : 0
% 12.60/5.11  
% 12.60/5.11  Ordering : KBO
% 12.60/5.11  
% 12.60/5.11  Simplification rules
% 12.60/5.11  ----------------------
% 12.60/5.11  #Subsume      : 391
% 12.60/5.11  #Demod        : 196
% 12.60/5.11  #Tautology    : 137
% 12.60/5.11  #SimpNegUnit  : 31
% 12.60/5.11  #BackRed      : 95
% 12.60/5.11  
% 12.60/5.11  #Partial instantiations: 0
% 12.60/5.11  #Strategies tried      : 1
% 12.60/5.11  
% 12.60/5.11  Timing (in seconds)
% 12.60/5.11  ----------------------
% 12.60/5.11  Preprocessing        : 0.37
% 12.60/5.11  Parsing              : 0.18
% 12.60/5.11  CNF conversion       : 0.03
% 12.60/5.11  Main loop            : 3.87
% 12.60/5.11  Inferencing          : 0.87
% 12.60/5.11  Reduction            : 0.83
% 12.60/5.11  Demodulation         : 0.54
% 12.60/5.11  BG Simplification    : 0.15
% 12.60/5.11  Subsumption          : 1.63
% 12.60/5.11  Abstraction          : 0.19
% 12.60/5.11  MUC search           : 0.00
% 12.60/5.11  Cooper               : 0.00
% 12.60/5.11  Total                : 4.27
% 12.60/5.11  Index Insertion      : 0.00
% 12.60/5.11  Index Deletion       : 0.00
% 12.60/5.11  Index Matching       : 0.00
% 12.60/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
