%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0827+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:54 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of leaves         :   32 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 200 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_400,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_404,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_163,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_167,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9'))
    | ~ r1_tarski('#skF_8',k1_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_8',k1_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_168,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_64])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_5'(A_12,B_13),A_12)
      | r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_40,plain,(
    r1_tarski(k6_relat_1('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [D_11,A_4] :
      ( r2_hidden(k4_tarski(D_11,D_11),k6_relat_1(A_4))
      | ~ r2_hidden(D_11,A_4)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [D_42,A_43] :
      ( r2_hidden(k4_tarski(D_42,D_42),k6_relat_1(A_43))
      | ~ r2_hidden(D_42,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_22,plain,(
    ! [C_16,B_13,A_12] :
      ( r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    ! [D_74,B_75,A_76] :
      ( r2_hidden(k4_tarski(D_74,D_74),B_75)
      | ~ r1_tarski(k6_relat_1(A_76),B_75)
      | ~ r2_hidden(D_74,A_76) ) ),
    inference(resolution,[status(thm)],[c_69,c_22])).

tff(c_207,plain,(
    ! [D_77] :
      ( r2_hidden(k4_tarski(D_77,D_77),'#skF_9')
      | ~ r2_hidden(D_77,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_199])).

tff(c_36,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(A_24,k1_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_210,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k1_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_77,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_207,c_36])).

tff(c_246,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_80,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_210])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_5'(A_12,B_13),B_13)
      | r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_290,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k1_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_5'(A_86,k1_relat_1('#skF_9')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_246,c_24])).

tff(c_298,plain,(
    r1_tarski('#skF_8',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_26,c_290])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_168,c_298])).

tff(c_304,plain,(
    ~ r1_tarski('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_405,plain,(
    ~ r1_tarski('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_304])).

tff(c_312,plain,(
    ! [D_96,A_97] :
      ( r2_hidden(k4_tarski(D_96,D_96),k6_relat_1(A_97))
      | ~ r2_hidden(D_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_415,plain,(
    ! [D_120,B_121,A_122] :
      ( r2_hidden(k4_tarski(D_120,D_120),B_121)
      | ~ r1_tarski(k6_relat_1(A_122),B_121)
      | ~ r2_hidden(D_120,A_122) ) ),
    inference(resolution,[status(thm)],[c_312,c_22])).

tff(c_423,plain,(
    ! [D_123] :
      ( r2_hidden(k4_tarski(D_123,D_123),'#skF_9')
      | ~ r2_hidden(D_123,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_415])).

tff(c_34,plain,(
    ! [B_25,C_26,A_24] :
      ( r2_hidden(B_25,k2_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_426,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k2_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_123,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_423,c_34])).

tff(c_465,plain,(
    ! [D_126] :
      ( r2_hidden(D_126,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_126,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_426])).

tff(c_531,plain,(
    ! [A_132] :
      ( r1_tarski(A_132,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_5'(A_132,k2_relat_1('#skF_9')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_465,c_24])).

tff(c_539,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_26,c_531])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_405,c_539])).

%------------------------------------------------------------------------------
