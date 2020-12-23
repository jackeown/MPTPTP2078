%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:46 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 252 expanded)
%              Number of leaves         :   18 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 712 expanded)
%              Number of equality atoms :    4 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    ! [B_30,A_31,C_32] :
      ( r1_tarski(B_30,k3_subset_1(A_31,C_32))
      | ~ r1_xboole_0(B_30,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_16])).

tff(c_85,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_75])).

tff(c_14,plain,(
    ! [B_13,A_12,C_15] :
      ( r1_tarski(B_13,k3_subset_1(A_12,C_15))
      | ~ r1_xboole_0(B_13,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_28,B_29] :
      ( k3_subset_1(A_28,k3_subset_1(A_28,B_29)) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_89,plain,(
    ! [B_13] :
      ( r1_tarski(B_13,'#skF_2')
      | ~ r1_xboole_0(B_13,k3_subset_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_13,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_158,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_161,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_167,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_293,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(k3_subset_1(A_45,C_46),k3_subset_1(A_45,B_47))
      | ~ r1_tarski(B_47,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [B_13,C_15,A_12] :
      ( r1_xboole_0(B_13,C_15)
      | ~ r1_tarski(B_13,k3_subset_1(A_12,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_378,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_xboole_0(k3_subset_1(A_49,C_50),B_51)
      | ~ m1_subset_1(k3_subset_1(A_49,C_50),k1_zfmisc_1(A_49))
      | ~ r1_tarski(B_51,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_293,c_12])).

tff(c_386,plain,(
    ! [B_51] :
      ( r1_xboole_0(k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')),B_51)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_51,k3_subset_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_378])).

tff(c_406,plain,(
    ! [B_52] :
      ( r1_xboole_0('#skF_2',B_52)
      | ~ r1_tarski(B_52,k3_subset_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_26,c_52,c_386])).

tff(c_417,plain,(
    ! [B_13] :
      ( r1_xboole_0('#skF_2',B_13)
      | ~ r1_xboole_0(B_13,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_13,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_406])).

tff(c_425,plain,(
    ! [B_53] :
      ( r1_xboole_0('#skF_2',B_53)
      | ~ r1_xboole_0(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_417])).

tff(c_438,plain,
    ( r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_425])).

tff(c_454,plain,(
    ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_438])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_173,plain,(
    ! [B_36,C_37,A_38] :
      ( r1_xboole_0(B_36,C_37)
      | ~ r1_tarski(B_36,k3_subset_1(A_38,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_185,plain,(
    ! [B_36] :
      ( r1_xboole_0(B_36,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_36,'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_36,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_173])).

tff(c_550,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_559,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_550])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_559])).

tff(c_607,plain,(
    ! [B_61] :
      ( r1_xboole_0(B_61,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_565,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_424,plain,(
    ! [B_13] :
      ( r1_xboole_0('#skF_2',B_13)
      | ~ r1_xboole_0(B_13,'#skF_2')
      | ~ m1_subset_1(B_13,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_417])).

tff(c_586,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_565,c_424])).

tff(c_593,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_200,plain,(
    ! [B_40,C_41,A_42] :
      ( r1_tarski(B_40,C_41)
      | ~ r1_tarski(k3_subset_1(A_42,C_41),k3_subset_1(A_42,B_40))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_209,plain,(
    ! [B_40] :
      ( r1_tarski(B_40,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1',B_40))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_40,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_200])).

tff(c_234,plain,(
    ! [B_43] :
      ( r1_tarski(B_43,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1',B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_209])).

tff(c_242,plain,(
    ! [C_15] :
      ( r1_tarski(C_15,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0('#skF_2',C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_234])).

tff(c_270,plain,(
    ! [C_44] :
      ( r1_tarski(C_44,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0('#skF_2',C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_242])).

tff(c_280,plain,(
    ! [C_44] :
      ( r1_xboole_0(C_44,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_xboole_0('#skF_2',C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_270,c_12])).

tff(c_291,plain,(
    ! [C_44] :
      ( r1_xboole_0(C_44,'#skF_2')
      | ~ r1_xboole_0('#skF_2',C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_280])).

tff(c_590,plain,
    ( r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_565,c_291])).

tff(c_606,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_590])).

tff(c_610,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_607,c_606])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_610])).

tff(c_621,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_673,plain,(
    ! [A_65] :
      ( r1_xboole_0(A_65,'#skF_2')
      | ~ r1_tarski(A_65,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_681,plain,(
    ! [B_13] :
      ( r1_xboole_0(B_13,'#skF_2')
      | ~ r1_xboole_0(B_13,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_13,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_673])).

tff(c_710,plain,(
    ! [B_67] :
      ( r1_xboole_0(B_67,'#skF_2')
      | ~ r1_xboole_0(B_67,'#skF_3')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_681])).

tff(c_726,plain,
    ( r1_xboole_0('#skF_4','#skF_2')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_710])).

tff(c_744,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_726])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.79/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.42  
% 2.79/1.44  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 2.79/1.44  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.79/1.44  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.79/1.44  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.79/1.44  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.79/1.44  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.79/1.44  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_70, plain, (![B_30, A_31, C_32]: (r1_tarski(B_30, k3_subset_1(A_31, C_32)) | ~r1_xboole_0(B_30, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.44  tff(c_16, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_75, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_16])).
% 2.79/1.44  tff(c_85, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_75])).
% 2.79/1.44  tff(c_14, plain, (![B_13, A_12, C_15]: (r1_tarski(B_13, k3_subset_1(A_12, C_15)) | ~r1_xboole_0(B_13, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.44  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.44  tff(c_41, plain, (![A_28, B_29]: (k3_subset_1(A_28, k3_subset_1(A_28, B_29))=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.44  tff(c_52, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.79/1.44  tff(c_89, plain, (![B_13]: (r1_tarski(B_13, '#skF_2') | ~r1_xboole_0(B_13, k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_13, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_14])).
% 2.79/1.44  tff(c_158, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_89])).
% 2.79/1.44  tff(c_161, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_158])).
% 2.79/1.44  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_161])).
% 2.79/1.44  tff(c_167, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_89])).
% 2.79/1.44  tff(c_293, plain, (![A_45, C_46, B_47]: (r1_tarski(k3_subset_1(A_45, C_46), k3_subset_1(A_45, B_47)) | ~r1_tarski(B_47, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.44  tff(c_12, plain, (![B_13, C_15, A_12]: (r1_xboole_0(B_13, C_15) | ~r1_tarski(B_13, k3_subset_1(A_12, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.44  tff(c_378, plain, (![A_49, C_50, B_51]: (r1_xboole_0(k3_subset_1(A_49, C_50), B_51) | ~m1_subset_1(k3_subset_1(A_49, C_50), k1_zfmisc_1(A_49)) | ~r1_tarski(B_51, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_293, c_12])).
% 2.79/1.44  tff(c_386, plain, (![B_51]: (r1_xboole_0(k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2')), B_51) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_51, k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_378])).
% 2.79/1.44  tff(c_406, plain, (![B_52]: (r1_xboole_0('#skF_2', B_52) | ~r1_tarski(B_52, k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_26, c_52, c_386])).
% 2.79/1.44  tff(c_417, plain, (![B_13]: (r1_xboole_0('#skF_2', B_13) | ~r1_xboole_0(B_13, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_13, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_406])).
% 2.79/1.44  tff(c_425, plain, (![B_53]: (r1_xboole_0('#skF_2', B_53) | ~r1_xboole_0(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_417])).
% 2.79/1.44  tff(c_438, plain, (r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_425])).
% 2.79/1.44  tff(c_454, plain, (~r1_xboole_0('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_85, c_438])).
% 2.79/1.44  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.44  tff(c_53, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.79/1.44  tff(c_173, plain, (![B_36, C_37, A_38]: (r1_xboole_0(B_36, C_37) | ~r1_tarski(B_36, k3_subset_1(A_38, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.44  tff(c_185, plain, (![B_36]: (r1_xboole_0(B_36, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_36, '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_36, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_53, c_173])).
% 2.79/1.44  tff(c_550, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_185])).
% 2.79/1.44  tff(c_559, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_550])).
% 2.79/1.44  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_559])).
% 2.79/1.44  tff(c_607, plain, (![B_61]: (r1_xboole_0(B_61, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_185])).
% 2.79/1.44  tff(c_565, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_185])).
% 2.79/1.44  tff(c_424, plain, (![B_13]: (r1_xboole_0('#skF_2', B_13) | ~r1_xboole_0(B_13, '#skF_2') | ~m1_subset_1(B_13, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_417])).
% 2.79/1.44  tff(c_586, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_565, c_424])).
% 2.79/1.44  tff(c_593, plain, (~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_586])).
% 2.79/1.44  tff(c_200, plain, (![B_40, C_41, A_42]: (r1_tarski(B_40, C_41) | ~r1_tarski(k3_subset_1(A_42, C_41), k3_subset_1(A_42, B_40)) | ~m1_subset_1(C_41, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.44  tff(c_209, plain, (![B_40]: (r1_tarski(B_40, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', B_40)) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_40, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_200])).
% 2.79/1.44  tff(c_234, plain, (![B_43]: (r1_tarski(B_43, k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_209])).
% 2.79/1.44  tff(c_242, plain, (![C_15]: (r1_tarski(C_15, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0('#skF_2', C_15) | ~m1_subset_1(C_15, k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_234])).
% 2.79/1.44  tff(c_270, plain, (![C_44]: (r1_tarski(C_44, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0('#skF_2', C_44) | ~m1_subset_1(C_44, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_242])).
% 2.79/1.44  tff(c_280, plain, (![C_44]: (r1_xboole_0(C_44, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_xboole_0('#skF_2', C_44) | ~m1_subset_1(C_44, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_270, c_12])).
% 2.79/1.44  tff(c_291, plain, (![C_44]: (r1_xboole_0(C_44, '#skF_2') | ~r1_xboole_0('#skF_2', C_44) | ~m1_subset_1(C_44, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_280])).
% 2.79/1.44  tff(c_590, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_565, c_291])).
% 2.79/1.44  tff(c_606, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_593, c_590])).
% 2.79/1.44  tff(c_610, plain, (~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_607, c_606])).
% 2.79/1.44  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_610])).
% 2.79/1.44  tff(c_621, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_586])).
% 2.79/1.44  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.44  tff(c_673, plain, (![A_65]: (r1_xboole_0(A_65, '#skF_2') | ~r1_tarski(A_65, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_621, c_2])).
% 2.79/1.44  tff(c_681, plain, (![B_13]: (r1_xboole_0(B_13, '#skF_2') | ~r1_xboole_0(B_13, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_13, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_673])).
% 2.79/1.44  tff(c_710, plain, (![B_67]: (r1_xboole_0(B_67, '#skF_2') | ~r1_xboole_0(B_67, '#skF_3') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_681])).
% 2.79/1.44  tff(c_726, plain, (r1_xboole_0('#skF_4', '#skF_2') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_710])).
% 2.79/1.44  tff(c_744, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_726])).
% 2.79/1.44  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_744])).
% 2.79/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  Inference rules
% 2.79/1.44  ----------------------
% 2.79/1.44  #Ref     : 0
% 2.79/1.44  #Sup     : 152
% 2.79/1.44  #Fact    : 0
% 2.79/1.44  #Define  : 0
% 2.79/1.44  #Split   : 17
% 2.79/1.44  #Chain   : 0
% 2.79/1.44  #Close   : 0
% 2.79/1.44  
% 2.79/1.44  Ordering : KBO
% 2.79/1.44  
% 2.79/1.44  Simplification rules
% 2.79/1.44  ----------------------
% 2.79/1.44  #Subsume      : 10
% 2.79/1.44  #Demod        : 87
% 2.79/1.44  #Tautology    : 37
% 2.79/1.44  #SimpNegUnit  : 12
% 2.79/1.44  #BackRed      : 0
% 2.79/1.44  
% 2.79/1.44  #Partial instantiations: 0
% 2.79/1.44  #Strategies tried      : 1
% 2.79/1.44  
% 2.79/1.44  Timing (in seconds)
% 2.79/1.44  ----------------------
% 2.79/1.44  Preprocessing        : 0.28
% 2.79/1.44  Parsing              : 0.16
% 2.79/1.44  CNF conversion       : 0.02
% 2.79/1.44  Main loop            : 0.39
% 2.79/1.44  Inferencing          : 0.14
% 2.79/1.44  Reduction            : 0.12
% 2.79/1.44  Demodulation         : 0.08
% 2.79/1.44  BG Simplification    : 0.02
% 2.79/1.44  Subsumption          : 0.09
% 2.79/1.44  Abstraction          : 0.02
% 2.79/1.44  MUC search           : 0.00
% 2.79/1.44  Cooper               : 0.00
% 2.79/1.44  Total                : 0.70
% 2.79/1.44  Index Insertion      : 0.00
% 2.79/1.44  Index Deletion       : 0.00
% 2.79/1.44  Index Matching       : 0.00
% 2.79/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
