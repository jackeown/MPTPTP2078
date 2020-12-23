%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:08 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 100 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_26,plain,(
    ! [A_26] : v1_relat_1(k1_wellord2(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_1] :
      ( k3_relat_1(k1_wellord2(A_1)) = A_1
      | ~ v1_relat_1(k1_wellord2(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_1] : k3_relat_1(k1_wellord2(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14])).

tff(c_104,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(k4_tarski('#skF_3'(A_58,B_59),'#skF_4'(A_58,B_59)),A_58)
      | r1_tarski(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [A_31,C_33,B_32] :
      ( r2_hidden(A_31,k3_relat_1(C_33))
      | ~ r2_hidden(k4_tarski(A_31,B_32),C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_3'(A_68,B_69),k3_relat_1(A_68))
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_104,c_36])).

tff(c_157,plain,(
    ! [A_1,B_69] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_1),B_69),A_1)
      | r1_tarski(k1_wellord2(A_1),B_69)
      | ~ v1_relat_1(k1_wellord2(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_154])).

tff(c_159,plain,(
    ! [A_1,B_69] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_1),B_69),A_1)
      | r1_tarski(k1_wellord2(A_1),B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_157])).

tff(c_34,plain,(
    ! [B_32,C_33,A_31] :
      ( r2_hidden(B_32,k3_relat_1(C_33))
      | ~ r2_hidden(k4_tarski(A_31,B_32),C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_129,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_4'(A_61,B_62),k3_relat_1(A_61))
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_104,c_34])).

tff(c_132,plain,(
    ! [A_1,B_62] :
      ( r2_hidden('#skF_4'(k1_wellord2(A_1),B_62),A_1)
      | r1_tarski(k1_wellord2(A_1),B_62)
      | ~ v1_relat_1(k1_wellord2(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_129])).

tff(c_134,plain,(
    ! [A_1,B_62] :
      ( r2_hidden('#skF_4'(k1_wellord2(A_1),B_62),A_1)
      | r1_tarski(k1_wellord2(A_1),B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_132])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_hidden(k4_tarski(A_27,B_28),k2_zfmisc_1(C_29,D_30))
      | ~ r2_hidden(B_28,D_30)
      | ~ r2_hidden(A_27,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_56,B_57),'#skF_4'(A_56,B_57)),B_57)
      | r1_tarski(A_56,B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_729,plain,(
    ! [A_151,C_152,D_153] :
      ( r1_tarski(A_151,k2_zfmisc_1(C_152,D_153))
      | ~ v1_relat_1(A_151)
      | ~ r2_hidden('#skF_4'(A_151,k2_zfmisc_1(C_152,D_153)),D_153)
      | ~ r2_hidden('#skF_3'(A_151,k2_zfmisc_1(C_152,D_153)),C_152) ) ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_759,plain,(
    ! [A_1,C_152] :
      ( ~ v1_relat_1(k1_wellord2(A_1))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_1),k2_zfmisc_1(C_152,A_1)),C_152)
      | r1_tarski(k1_wellord2(A_1),k2_zfmisc_1(C_152,A_1)) ) ),
    inference(resolution,[status(thm)],[c_134,c_729])).

tff(c_776,plain,(
    ! [A_154,C_155] :
      ( ~ r2_hidden('#skF_3'(k1_wellord2(A_154),k2_zfmisc_1(C_155,A_154)),C_155)
      | r1_tarski(k1_wellord2(A_154),k2_zfmisc_1(C_155,A_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_759])).

tff(c_829,plain,(
    ! [A_1] : r1_tarski(k1_wellord2(A_1),k2_zfmisc_1(A_1,A_1)) ),
    inference(resolution,[status(thm)],[c_159,c_776])).

tff(c_38,plain,(
    ~ r1_tarski(k1_wellord2('#skF_5'),k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_38])).

%------------------------------------------------------------------------------
